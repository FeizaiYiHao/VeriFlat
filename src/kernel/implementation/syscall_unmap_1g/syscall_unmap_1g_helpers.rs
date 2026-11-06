use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_unmap_1g_trace::*;
use super::syscall_unmap_1g_exit::unmap_1g_release_and_exit;
use super::syscall_unmap_1g_range::unmap_1g_range;

verus! {
/// With cpu `cpu_id`, its running thread, and the pagetable `pagetable` of the thread's process write-held since the entry snapshot `entry_lctx` was aligned with, and every page of `va_range` a present 1G leaf: records the progress, enters the kernel step, unmaps the range, clears the
/// progress, releases every lock, and records the exiting step.
pub(super) fn unmap_1g_unmap_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, len: usize, va_range: &VaRange1G,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, Ghost(entry_lctx): Ghost<LocalContext>,
    Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>, Tracked(pagetable_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        !(len == 0 || len > usize::MAX / 0x40000000 || !spec_va_1g_valid(va) || va >= usize::MAX - len * 0x40000000 || !spec_va_1g_range_valid(va, len)),
        *va_range == spec_va_range_1g(va, len),
        va_range.wf(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, pt_mp: old(krnl).pt_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
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
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        old(krnl).ctn_mp.dom().contains(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(va_range.view()[j])
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().spec_index(va_range.view()[j]).present
        },
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
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
        unmap_1g_syscall_trace(final(steps).view(), cpu_id, va, len),
        RetValueType::Success == unmap_1g_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, len),
        final(krnl).pt_mp.dom().contains(pagetable),
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < len ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(va_range.view()[j]),
{
    proof {
        broadcast use spec_va_1g_valid_index_roundtrip;
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr);
        process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::Unmap1g { range: *va_range, unmapped: 0, flushed: false })), Tracked(&*lctx), Tracked(&thread_perm));
    proof {
        let ghost entered_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        assert(unmap_1g_trace_after_enter(steps.view(), cpu_id, *va_range)) by {
            unmap_1g_result_from_k(&old(steps).snapshot_k(), cpu_id, va, len, RetValueType::Success);
            kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(&old(steps).snapshot_k(), &entered_k, &entry_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable);
            unmap_1g_enter_step_from_u(&old(steps).snapshot_k(), kernel_k_to_kernel_u(entered_k), cpu_id, prc_ptr, thrd_ptr, pagetable, va, len, *va_range);
            unmap_1g_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(entered_k), cpu_id, *va_range);
        };
        cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id);
    }
    let ghost entered = steps.view();
    unmap_1g_range(krnl, va_range, pagetable, thrd_ptr, cpu_id, cr3, pcid, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cpu_perm), Tracked(&thread_perm), Tracked(&pagetable_perm));
    proof { assert(unmap_1g_trace_after_range(steps.view(), cpu_id, *va_range)) by { unmap_1g_trace_range_steps(&*steps, entered, cpu_id, *va_range); }; }
    unmap_1g_release_and_exit(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, len, va_range, prc_ptr, thrd_ptr, pagetable, Tracked(cpu_perm), Tracked(thread_perm),
        Tracked(pagetable_perm));
    proof { unmap_1g_result_from_k(&old(steps).snapshot_k(), cpu_id, va, len, RetValueType::Success); }
}
} // verus!
