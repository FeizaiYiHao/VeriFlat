use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_2m_spec::*;
use super::syscall_unmap_2m_trace::*;

verus! {
/// After the range of a successful unmap is cleared and flushed, with cpu `cpu_id` and its running thread write-held, the
/// pagetable `pagetable` of the thread's process read-held, and the 2M windows of `cover`, the 4K range covering `va_range`, whose
/// L3 entry links an L2 page held through `window_perms`: clears the progress, releases every lock, and records the exiting step.
/// The 2M mapping does not change.
pub(super) fn unmap_2m_release_and_exit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, len: usize, va_range: &VaRange2M,
    cover: &VaRange4K,     prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>,
    Tracked(pagetable_perm): Tracked<LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        unmap_2m_trace_after_range(old(steps).view(), cpu_id, *va_range),
        len > 0,
        *va_range == unmap_2m_syscall_va_range(va, len),
        va_range.wf(),
        *cover == va_range.covering_4k_range(),
        cover.wf(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_perm.lock_id() }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        cpu_perm.state() is WriteLock,
        cpu_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range: *va_range, unmapped: len, flushed: true }),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= spec_va2index(va).0,
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.lock_id()),
        pagetable_perm.state() is ReadLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        forall|w: WindowVa|
            #![trigger va_range_2m_windows(*cover).contains(w)]
            va_range_2m_windows(*cover).contains(w) && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            ==> window_perms.dom().contains(w),
        forall|w: WindowVa|
            #![trigger window_perms.dom().contains(w)]
            window_perms.dom().contains(w) ==> {
                &&& va_range_2m_windows(*cover).contains(w)
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, w), TypedLockMode::Write)
                &&& window_perms.index(w).state() is WriteLock
                &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                    == (RwLockState::Write { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_leaves_present(w)
                &&& !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
                &&& !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable && window_perms.dom().contains(w)),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
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
        unmap_2m_syscall_trace(final(steps).view(), cpu_id, va, len),
        final(krnl).pt_mp.dom().contains(pagetable),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
{
    let ghost range_steps = steps.view();
    let ghost exit_start = *krnl;
    let ghost exit_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
    krnl.unlock_pagetable_range_existing_windows(pagetable, cover, Tracked(&pagetable_perm), Tracked(&mut *lctx), Tracked(window_perms));
    proof { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    krnl.runlock_pagetable(cpu_id, pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        let ghost exit_k = *krnl;
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thrd_ptr);
        assert(unmap_2m_syscall_trace(steps.view(), cpu_id, va, len)) by {
            process_thread_wf_thread_at(exit_start.prc_mp, exit_start.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(exit_start.prc_mp, exit_start.pt_mp, prc_ptr);
            kernel_cpu_thread_unlocked_pagetable_runlocked_and_progress_changed_implies_u_step(&exit_start, &exit_k, &exit_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable);
            unmap_2m_exit_step_from_u(&exit_start, kernel_k_to_kernel_u(exit_k), cpu_id, prc_ptr, thrd_ptr, pagetable, *va_range, exit_k.pt_mp.spec_index(pagetable).lock_state_u(),
                whole_pagetable(exit_k.pt_mp, exit_k.pt_lower.view(), pagetable).lower.pagetable_window_locks);
            unmap_2m_trace_exit_step(&*steps, range_steps, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, va, len);
        };
    }
}
} // verus!
