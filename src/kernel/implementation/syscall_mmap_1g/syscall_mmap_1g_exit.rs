use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_trace::*;

verus! {
/// After every page of a successful mmap is mapped, with cpu `cpu_id`, its running thread, and the pagetable `pagetable` of the thread's process write-held: clears the progress, releases every lock, and records the exiting step. The 1G mapping does not change.
pub(super) fn mmap_1g_release_and_exit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, len: usize, va_range: &VaRange1G,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>,
    Tracked(pagetable_perm): Tracked<LockPerm>, Ghost(hidden): Ghost<bool>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        mmap_1g_trace_after_range(old(steps).view(), cpu_id, *va_range),
        *va_range == spec_va_range_1g(va, len),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_perm.lock_id() }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        cpu_perm.state() is WriteLock,
        cpu_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *va_range, mapped: len, directory: false, hidden, flushed: hidden }),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
            ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
            ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
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
        mmap_1g_syscall_trace(final(steps).view(), cpu_id, va, len),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
{
    let ghost range_steps = steps.view();
    let ghost exit_start = *krnl;
    let ghost exit_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
    proof { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        let ghost exit_k = *krnl;
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thrd_ptr);
        assert(mmap_1g_syscall_trace(steps.view(), cpu_id, va, len)) by {
            process_thread_wf_thread_at(exit_start.prc_mp, exit_start.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(exit_start.prc_mp, exit_start.pt_mp, prc_ptr);
            process_cpu_wf_at(exit_start.prc_mp, exit_start.cpu_arr, cpu_id);
            exit_start.pt_mp.typed_lock_map_aligned_write_at(exit_lctx.pagetable_lock_map(), exit_lctx.thread_id(), pagetable);
            kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(&exit_start, &exit_k, &exit_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable);
            mmap_1g_exit_step_from_u(&exit_start, kernel_k_to_kernel_u(exit_k), cpu_id, prc_ptr, thrd_ptr, pagetable);
            mmap_1g_trace_exit_step(&*steps, range_steps, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, va, len);
        };
    }
}
} // verus!
