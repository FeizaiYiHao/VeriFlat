use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_2m_spec::*;
use super::syscall_mmap_2m_trace::*;

verus! {
/// With every page of `va_range` mapped by a present, writable, executable 2M leaf of the read-held pagetable, while holding
/// `cpu_id`, its current `thrd_ptr` and the 2M windows of the range: clears the thread's progress, releases the windows, the
/// pagetable, the thread and the cpu, and records the exit step that completes the syscall trace.
pub(super) fn mmap_2m_unlock_range_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange2M,
    thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, Ghost(enter_phase): Ghost<Mmap2mPhase>, Ghost(flushed): Ghost<bool>,
    Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        range > 0,
        va_4k_valid(va),
        *va_range == mmap_2m_syscall_va_range(va, range),
        va_range.wf(),
        enter_phase is Read || enter_phase is Fill,
        mmap_2m_trace_after_range(old(steps).view(), cpu_id, *va_range, enter_phase),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m {
            range: *va_range, mapped: range, directory: Mmap2mDirectory::None, phase: if enter_phase is Read { Mmap2mPhase::Read } else { Mmap2mPhase::Filled }, flushed
        }),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va_range.start),
        va_range.covering_4k_range().wf(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_mapping_4k_va_range_windows_exist(&va_range.covering_4k_range()),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(va_range.covering_4k_range()).contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(va_range.covering_4k_range()).contains(w)] va_range_2m_windows(va_range.covering_4k_range()).contains(w) ==> {
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let l2_page = table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va));
            &&& window_perms.dom().contains(w)
            &&& window_perms.index(w).state() is WriteLock
            &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
            &&& table.lower.l2_owner(l2_page, spec_v2l2index(w.va)) == (RwLockState::Write { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
            &&& table.window_leaves_present(w)
            &&& !table.lower.window_stale_cpus.dom().contains((l2_page, spec_v2l2index(w.va)))
            &&& !table.lower.l2_entry_hides_l1(l2_page, spec_v2l2index(w.va))
        },
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            let post = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.mapping_2m().dom().contains(va_range.view()[j])
            &&& post.mapping_2m().spec_index(va_range.view()[j]).present
            &&& post.mapping_2m().spec_index(va_range.view()[j]).write
            &&& !post.mapping_2m().spec_index(va_range.view()[j]).execute_disable
        },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
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
        final(steps).view().len() == old(steps).view().len() + 1,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        mmap_2m_syscall_trace(final(steps).view(), cpu_id, va, range, enter_phase),
        mmap_2m_syscall_success_mapped(final(krnl), cpu_id, va, range),
{
    let ghost cover = va_range.covering_4k_range();
    let ghost range_steps = steps.view();
    let ghost exit_start = *krnl;
    let ghost exit_lctx = *lctx;
    let cover_exec = VaRange4K { start: va_range.start, len: range * 512, view: Ghost(va_range.covering_4k_range().view@) };
    assert(cover_exec == cover);
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_lock_perm));
    krnl.unlock_pagetable_range_windows(pagetable_ptr, &cover_exec, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx), Tracked(window_perms));
    proof { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    krnl.runlock_pagetable(cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    proof { cpu_op_wf_at(old(krnl).cpu_op.view().view(), old(krnl).cpu_arr, cpu_id); cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    let ghost exit_k = *krnl;
    proof {
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thrd_ptr);
        assert(mmap_2m_syscall_trace(steps.view(), cpu_id, va, range, enter_phase)) by {
            kernel_cpu_thread_unlocked_pagetable_runlocked_and_progress_changed_implies_u_step(&exit_start, &exit_k, &exit_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable_ptr);
            process_cpu_wf_at(exit_start.prc_mp, exit_start.cpu_arr, cpu_id); process_pagetable_wf_process_at(exit_start.prc_mp, exit_start.pt_mp, prc_ptr);
            mmap_2m_exit_step_from_u(&exit_start, kernel_k_to_kernel_u(exit_k), cpu_id, prc_ptr, thrd_ptr, pagetable_ptr, *va_range,
                whole_pagetable(exit_k.pt_mp, exit_k.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks);
            mmap_2m_trace_exit_step(&*steps, range_steps, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, va, range, enter_phase);
        };
        assert(mmap_2m_syscall_success_mapped(krnl, cpu_id, va, range)) by { va_range.wf_implies_view_index_is_start_plus_offset(); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); };
    }
}
} // verus!
