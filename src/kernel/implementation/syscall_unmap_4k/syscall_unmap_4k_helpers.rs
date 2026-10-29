use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;
use super::syscall_unmap_4k_trace::*;

verus! {
/// With cpu `cpu_id`, its container, process, and running thread write-held and the process pagetable `pagetable` read-held
/// since the entry snapshot `entry_lctx` was aligned with, the 2M windows of `va_range` whose L3 entry links an L2 page held
/// through `window_perms`, and every page of `va_range` mapped: records the progress, enters the kernel step, unmaps the range,
/// clears the progress, releases every lock, and records the exiting step. Inside the windows of the range only its pages change.
pub(super) fn unmap_4k_unmap_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
    container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid,
    Ghost(entry_lctx): Ghost<LocalContext>, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(container_perm): Tracked<LockPerm>, Tracked(process_perm): Tracked<LockPerm>,
    Tracked(thread_perm): Tracked<LockPerm>, Tracked(pagetable_perm): Tracked<LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
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
        *va_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) }),
        va_range.wf(),
        *old(krnl) == (KernelK {
            cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower,
            ..old(steps).snapshot_k()
        }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
        old(krnl).pt_lower.view() =~= old(steps).snapshot_k().pt_lower.view().insert(pagetable, old(krnl).pt_lower.view().spec_index(pagetable)),
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
        ({
            let pre = old(steps).snapshot_k().ctn_mp.spec_index(container_ptr);
            let post = old(krnl).ctn_mp.spec_index(container_ptr);
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: container_perm.lock_id() })
            &&& post.lock_process_owner_u() == Some(LockOwnerId::Some(old(steps).snapshot_k().prc_mp.spec_index(process_ptr).view_rodata().view().depth))
            &&& post.view() == pre.view()
            &&& post.view_rodata() == pre.view_rodata()
            &&& post.view_ghost() == pre.view_ghost()
            &&& post.being_killed() == pre.being_killed()
            &&& container_perm.state() is WriteLock
            &&& container_perm.thread_id() == old(lctx).thread_id()
        }),
        wlock_ensures(old(steps).snapshot_k().prc_mp.spec_index(process_ptr), old(krnl).prc_mp.spec_index(process_ptr), old(steps).snapshot_k().prc_mp.lock_id_by_key(process_ptr), old(lctx), process_perm),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_perm),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable).wlocked(),
        old(krnl).pt_mp.spec_index(pagetable).view() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).view(),
        old(krnl).pt_mp.spec_index(pagetable).being_killed() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).being_killed(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.lock_id()),
        pagetable_perm.state() is ReadLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_4k(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_1g(),
        forall|w: WindowVa|
            #![trigger va_range_2m_windows(*va_range).contains(w)]
            va_range_2m_windows(*va_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            ==> window_perms.dom().contains(w),
        forall|w: WindowVa|
            #![trigger window_perms.dom().contains(w)]
            window_perms.dom().contains(w) ==> {
                &&& va_range_2m_windows(*va_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, w), TypedLockMode::Write)
                &&& window_perms.index(w).state() is WriteLock
                &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &window_perms.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable && window_perms.dom().contains(w)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(container_ptr).view().zombie,
        !old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pcid == pcid,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        forall|j: int| #![trigger va_range.view().spec_index(j)] 0 <= j < va_range.len ==> {
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va_range.view().spec_index(j))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va_range.view().spec_index(j)).present
        },
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
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
        range + 3 <= final(steps).nonlock_view().len() <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4,
        unmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range),
        RetValueType::Success == unmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range),
        final(krnl).pt_mp.dom().contains(pagetable),
        forall|j: int| #![trigger va_range.view().spec_index(j)] 0 <= j < range ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va_range.view().spec_index(j)),
        forall|j: int, v: VAddr|
            #![trigger va_range.view().spec_index(j), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger va_range.view().spec_index(j), pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            0 <= j < range && spec_v2l4index(v) == spec_v2l4index(va_range.view().spec_index(j)) && spec_v2l3index(v) == spec_v2l3index(va_range.view().spec_index(j))
                && spec_v2l2index(v) == spec_v2l2index(va_range.view().spec_index(j)) && !va_range.view().contains(v) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_1g(),
{
    let ghost checked_table = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Unmap4k { range: *va_range, unmapped: 0, flushed: false })), Tracked(&*lctx), Tracked(&thread_perm));
    proof {
        let ghost entered_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(unmap_4k_trace_after_enter(steps.view(), cpu_id, *va_range)) by {
            unmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Success);
            kernel_thread_context_wlocked_pagetable_rlocked_and_progress_changed_implies_u_step(&old(steps).snapshot_k(), &entered_k, &entry_lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable);
            unmap_4k_enter_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, container_ptr, process_ptr, thread_ptr, *va_range);
            unmap_4k_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, *va_range);
        };
    }
    let ghost entered = steps.view();
    unmap_4k_range(krnl, va_range, pagetable, thread_ptr, cpu_id, cr3, pcid, Ghost(checked_table), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cpu_perm), Tracked(&thread_perm), Tracked(&pagetable_perm));
    let ghost range_steps = steps.view();
    let ghost exit_start = *krnl;
    let ghost exit_lctx = *lctx;
    proof { assert(unmap_4k_trace_after_range(range_steps, cpu_id, *va_range)) by { unmap_4k_trace_range_steps(&*steps, entered, cpu_id, *va_range); }; }
    assert(va_range.view() =~= Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) by { va_range.va_range_lemma(); };
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
    krnl.unlock_pagetable_range_existing_windows(pagetable, va_range, Tracked(&pagetable_perm), Tracked(&mut *lctx), Tracked(window_perms));
    proof { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    krnl.runlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
    assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        let ghost exit_k = *krnl;
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thread_ptr);
        assert(unmap_4k_syscall_trace(steps.view(), cpu_id, va, range)) by {
            kernel_thread_context_unlocked_pagetable_runlocked_and_progress_changed_implies_u_step(&exit_start, &exit_k, &exit_lctx, cpu_id, container_ptr, process_ptr, thread_ptr, pagetable);
            unmap_4k_exit_step_from_u(kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, container_ptr, process_ptr, thread_ptr, exit_k.pt_mp.spec_index(pagetable).lock_state_u());
            unmap_4k_trace_exit_step(&*steps, range_steps, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, va, range);
        };
        unmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Success);
    }
}
} // verus!
