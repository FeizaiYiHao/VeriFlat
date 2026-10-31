use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_4k_map_range::mmap_4k_map_leaves_and_finish;
use super::syscall_mmap_4k_precheck::{mmap_4k_precheck, Mmap4kPrecheck};
use super::syscall_mmap_4k_read_enter::mmap_4k_unlock_read_rejected;
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::*;

verus! {
/// With `pagetable_ptr` just read-locked through `pagetable_lock_perm` from `pre_k` and `pre_lctx`, which met the entry
/// conditions of the read section, `va_range` above the kernel L4 entries and every 2M window of it present: holds those
/// windows and maps the range with the recorded steps when it is free, or releases every lock and finishes without recording
/// a step when it is not.
pub(super) fn mmap_4k_read_lock_windows_and_map(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
    alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pre_k): Ghost<KernelK>, Ghost(pre_lctx): Ghost<LocalContext>, Tracked(pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == pre_lctx.cpu_id(),
        pre_k.inv(),
        pre_lctx.kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(&pre_k, &pre_lctx),
        old(steps).view().len() == 0,
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &pre_k),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, pre_k.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &pre_k),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        *va_range == mmap_4k_syscall_va_range(va, range),
        va_range.wf(),
        va_range.len > 0,
        pre_k == (KernelK { cpu_arr: pre_k.cpu_arr, cpu_op: pre_k.cpu_op, thr_mp: pre_k.thr_mp, ..old(steps).snapshot_k() }),
        pre_k.cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        pre_k.cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        pre_k.cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().locked(),
        pre_k.cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: pre_lctx.thread_id(), lock_id: cpu_lock_perm.lock_id() }),
        pre_k.cpu_arr.spec_index(cpu_id).view().being_killed() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre_k.cpu_arr.spec_index(cpu_id).view().killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().killer_info(),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == pre_lctx.thread_id(),
        !pre_k.cpu_arr.spec_index(cpu_id).view().being_killed(),
        pre_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        pre_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        pre_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        pre_k.cpu_hw_cr3_pcid[cpu_id as int].view() == (pre_k.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pre_k.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        pre_k.ctn_mp.dom().contains(container_ptr),
        pre_k.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        pre_k.allc_4k_mp.dom().contains(alloc_ptr_4k),
        pre_k.prc_mp.dom().contains(process_ptr),
        !pre_k.prc_mp.spec_index(process_ptr).view().zombie,
        pre_k.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre_k.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        pre_k.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        pre_k.thr_mp.dom().contains(thread_ptr),
        pre_k.thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), pre_k.thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), &pre_lctx, thread_lock_perm),
        !pre_k.thr_mp.spec_index(thread_ptr).being_killed(),
        pre_k.thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        pre_k.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        pre_k.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        pre_k.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        pre_k.thr_mp.spec_index(thread_ptr).view().quota_4k >= 4 * range,
        pre_k.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        pre_k.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        pre_k.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !pre_k.thr_mp.spec_index(thread_ptr).view_ghost().exited,
        pre_k.pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(pre_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(pre_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        pre_lctx.cpu_lock_map().dom() =~= set![cpu_id],
        pre_lctx.thread_lock_map().dom() =~= set![thread_ptr],
        pre_lctx.pagetable_lock_map().dom().is_empty(),
        pre_lctx.pagetable_window_lock_map().dom().is_empty(),
        pre_lctx.page_lock_map().dom().is_empty(),
        pre_lctx.container_lock_map().dom().is_empty(),
        pre_lctx.process_lock_map().dom().is_empty(),
        pre_lctx.endpoint_lock_map().dom().is_empty(),
        pre_lctx.scheduler_lock_map().dom().is_empty(),
        pre_lctx.pcid_allocator_lock_map().dom().is_empty(),
        pre_lctx.cpu_set_lock_map().dom().is_empty(),
        pre_lctx.iommu_table_lock_map().dom().is_empty(),
        pre_lctx.iommu_root_table_lock_map().dom().is_empty(),
        pre_lctx.allocator_quota_4k_lock_map().dom().is_empty(),
        pre_lctx.allocator_cache_4k_lock_map().dom().is_empty(),
        pre_lctx.allocator_global_pool_4k_lock_map().dom().is_empty(),
        pre_lctx.allocator_quota_2m_lock_map().dom().is_empty(),
        pre_lctx.allocator_cache_2m_lock_map().dom().is_empty(),
        pre_lctx.allocator_global_pool_2m_lock_map().dom().is_empty(),
        pre_lctx.allocator_quota_1g_lock_map().dom().is_empty(),
        pre_lctx.allocator_cache_1g_lock_map().dom().is_empty(),
        pre_lctx.allocator_global_pool_1g_lock_map().dom().is_empty(),
        pre_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
        pre_lctx.pcid_needflush_lock_map().dom().is_empty(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).hidden_leaves_in_locked_windows(),
        old(lctx).cpu_id() == pre_lctx.cpu_id(),
        old(krnl).inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre_k, old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(pre_k.ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre_k, old(krnl)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, ..pre_k }),
        old(krnl).pt_mp.unchanged_except(&pre_k.pt_mp, pagetable_ptr),
        old(krnl).pt_mp.lock_id_by_key(pagetable_ptr) == pre_k.pt_mp.lock_id_by_key(pagetable_ptr),
        forall|other_pagetable: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.lock_id_by_key(other_pagetable)] other_pagetable != pagetable_ptr && pre_k.pt_mp.dom().contains(other_pagetable)
            ==> old(krnl).pt_mp.dom().contains(other_pagetable) && old(krnl).pt_mp.lock_id_by_key(other_pagetable) == pre_k.pt_mp.lock_id_by_key(other_pagetable),
        old(lctx).thread_id() == pre_lctx.thread_id(),
        old(lctx).kernel_view_locking_state() == pre_lctx.kernel_view_locking_state(),
        rlock_ensures(pre_k.pt_mp.spec_index(pagetable_ptr), old(krnl).pt_mp.spec_index(pagetable_ptr), pre_k.pt_mp.lock_id_by_key(pagetable_ptr), old(lctx), pagetable_lock_perm),
        typed_lock_maps_inserted(&pre_lctx, old(lctx), KernelObjId::PageTable(pagetable_ptr), TypedHeldLock { lock_id: old(krnl).pt_mp.lock_id_by_key(pagetable_ptr), mode: TypedLockMode::Read }),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_va2index(va).0,
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_windows_exist(va_range),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).no_locks_held(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).all_objects_unlocked(final(lctx)),
        ret == mmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range),
        ret is Success ==> mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, Mmap4kPhase::Read) && kernel_k_to_kernel_u(old(steps).snapshot_k()) == final(steps).view()[0].old_u,
        ret is Success ==> mmap_4k_syscall_success_mapped(final(krnl), cpu_id, va, range),
        !(ret is Success) ==> final(steps).view().len() == 0,
{
    proof {
        pre_k.pt_mp.typed_lock_map_aligned_locked_at(pre_lctx.pagetable_lock_map(), pre_lctx.thread_id(), pagetable_ptr); pagetable_perms_wf_map(pre_k.pt_mp); pagetable_perms_wf_at(pre_k.pt_mp, pagetable_ptr);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    }
    let ghost unlocked_windows = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks;
    let Tracked(window_perms) = krnl.lock_pagetable_range_windows(pagetable_ptr, va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx));
    let ghost checked = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let (precheck, Ghost(found)) = mmap_4k_precheck(krnl, va_range, pagetable_ptr, Tracked(&*lctx), Tracked(&pagetable_lock_perm));
    let ready = match precheck { Mmap4kPrecheck::Ready => true, _ => false };
    if !ready {
        krnl.unlock_pagetable_range_windows(pagetable_ptr, va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx), Tracked(window_perms));
        proof { assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks =~= unlocked_windows); }
        mmap_4k_unlock_read_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thread_ptr, pagetable_ptr, Tracked(pagetable_lock_perm), Tracked(thread_lock_perm),
            Tracked(cpu_lock_perm));
        proof { mmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::ErrorVaInUse, Some(checked), found); }
        return RetValueType::ErrorVaInUse;
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
            mmap_4k_enter_step_from_u(&old(steps).snapshot_k(), kernel_k_to_kernel_u(entered_k), cpu_id, process_ptr, thread_ptr, pagetable_ptr, va, range, *va_range,
                Mmap4kPhase::Read, pagetable_c(entered_k.pt_mp, entered_k.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks);
            mmap_4k_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, *va_range, Mmap4kPhase::Read);
        };
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        broadcast use spec_va_2m_valid_index_roundtrip;
    }
    let ghost entered = steps.view();
    mmap_4k_map_leaves_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, pagetable_ptr,
        Ghost(Mmap4kPhase::Read), Ghost(entered), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(cpu_lock_perm), Tracked(window_perms));
    RetValueType::Success
}
} // verus!
