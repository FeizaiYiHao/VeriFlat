use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal};
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_pci_bar_unmap_4k_trace::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::{unmap_4k_present::clear_4k_mapping_present, unmap_4k_flush_all::flush_pagetable_tlbs, unmap_io_leaf::remove_io_4k_mapping};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::{unmap_4k_present::clear_4k_mapping_present, unmap_4k_flush_all::flush_pagetable_tlbs, unmap_io_leaf::remove_io_4k_mapping};

verus! {
/// With cpu `cpu_id`, its running thread, and the pagetable `pagetable` of the thread's process write-held since the entry snapshot
/// `entry_lctx` was aligned with, and `va` a present IO 4K leaf mapping `addr`: hides the leaf and records the hide step, flushes the
/// process's PCID on every cpu, records the flush, removes the leaf and its BAR mapping, releases every lock, and records the exit step.
pub(super) fn unmap_pci_bar_4k_unmap_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, addr: PAddr, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid, Ghost(entry_lctx): Ghost<LocalContext>, Tracked(cpu_perm): Tracked<LockPerm>,
    Tracked(thread_perm): Tracked<LockPerm>, Tracked(pagetable_perm): Tracked<LockPerm>,
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
        va_4k_valid(va),
        ({
            let s = old(steps).snapshot_k();
            let cpu = s.cpu_arr.spec_index(cpu_id).view();
            let thread = s.thrd_mp.spec_index(thrd_ptr);
            let table = whole_pagetable(s.pt_mp, s.pt_lower.view(), pagetable);
            &&& cpu.view().view().state is Running
            &&& !cpu.being_killed()
            &&& cpu.view().view().current_thread == Some(thrd_ptr)
            &&& cpu.view().view().current_process == Some(prc_ptr)
            &&& s.thrd_mp.dom().contains(thrd_ptr)
            &&& !thread.being_killed()
            &&& thread.view().owning_proc == prc_ptr
            &&& thread.view().state == (ThreadState::RUNNING { cpu_id })
            &&& s.ctn_mp.dom().contains(thread.view().owning_container)
            &&& s.prc_mp.dom().contains(prc_ptr)
            &&& !s.prc_mp.spec_index(prc_ptr).view().zombie
            &&& s.prc_mp.spec_index(prc_ptr).view().pagetable == pagetable
            &&& s.pt_mp.dom().contains(pagetable)
            &&& table.mapping_4k().dom().contains(va) && table.mapping_4k()[va].present && table.mapping_4k()[va].is_io
            &&& table.mapping_4k()[va].addr == addr
        }),
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
            &&& post.view().kernel_call_perm() is None
            &&& post.being_killed() == pre.being_killed()
            &&& post.killer_info() == pre.killer_info()
            &&& cpu_perm.state() is WriteLock
            &&& cpu_perm.thread_id() == old(lctx).thread_id()
        }),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_perm),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable).locked(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: pagetable_perm.lock_id() }),
        old(krnl).pt_mp.spec_index(pagetable).view().higher == old(steps).snapshot_k().pt_mp.spec_index(pagetable).view().higher,
        old(krnl).pt_mp.spec_index(pagetable).being_killed() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).being_killed(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i)
                ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
        !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index|
            #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some,
        !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index, l3i: L3Index|
            #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l3(l4i, l3i) is Some,
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
        old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        old(krnl).ctn_mp.dom().contains(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view().exited.view(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k()[va].present,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k()[va].is_io,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k()[va].addr == addr,
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
        unmap_pci_bar_4k_syscall_trace(final(steps).view(), cpu_id, va),
{
    let ghost entry = old(steps).snapshot_k();
    let ghost locked = *krnl;
    assert(!(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is Zombie)) by {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
    };
    let ghost ctn_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container;
    let indices = va2index(va);
    proof {
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    // hide step: the leaf leaves the user mapping under the three locks taken since the entry
    clear_4k_mapping_present(krnl, pagetable, va, Tracked(&mut *lctx), Tracked(&pagetable_perm));
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::UnmapPciBar4k { va, flushed: false })), Tracked(&*lctx), Tracked(&thread_perm));
    let ghost hidden = *krnl;
    proof {
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
    }
    // flush steps
    let ghost hide_steps_snap = *steps;
    let ghost hidden_steps = steps.view();
    let ghost flush_entry = *krnl;
    let ghost flush_lctx = *lctx;
    flush_pagetable_tlbs::<true>(krnl, pagetable, cr3, pcid, cpu_id, thrd_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&cpu_perm), Tracked(&pagetable_perm));
    let ghost flush_steps_snap = *steps;
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
    }
    // flushed step
    let ghost flushed_steps = steps.view();
    let ghost flushed_snap = steps.snapshot_k();
    let ghost flushed_pre = *krnl;
    let ghost flushed_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::UnmapPciBar4k { va, flushed: true })), Tracked(&*lctx), Tracked(&thread_perm));
    let ghost flushed_k = *krnl;
    proof { krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr); }
    // exit step: remove the leaf in its window, clear the progress, and release every lock
    let ghost exit_steps = steps.view();
    let ghost exit_start = *krnl;
    let ghost window_va = WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) };
    proof {
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        spec_va_4k_index_roundtrip_at(window_va.va, indices.0, indices.1, indices.2, 0usize);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c.wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        let (l4i, l3i, l2i) = (indices.0, indices.1, indices.2);
        assert(page_table_key_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    let Tracked(window_perm) = krnl.lock_pagetable_window::<true>(pagetable, indices.0, indices.1, indices.2, Tracked(&pagetable_perm), Tracked(&mut *lctx));
    remove_io_4k_mapping(krnl, pagetable, va, addr, Tracked(&mut *lctx), Tracked(&pagetable_perm), Tracked(&window_perm));
    krnl.unlock_pagetable_window::<true>(pagetable, indices.0, indices.1, indices.2, Tracked(&pagetable_perm), Tracked(&mut *lctx), Tracked(window_perm));
    let ghost removed = *krnl;
    let ghost removed_lctx = *lctx;
    proof {
        broadcast use typed_lock_map_insert_absent_then_remove_implies_unchanged;
        let c = whole_pagetable(exit_start.pt_mp, exit_start.pt_lower.view(), pagetable);
        assert_maps_equal!(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.pagetable_window_locks, c.lower.pagetable_window_locks);
        assert_maps_equal!(krnl.pt_lower.view(), exit_start.pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
    }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
    proof { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(&entry, &locked, &entry_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable);
        kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(&locked, &hidden, pagetable, va, thrd_ptr);
        process_cpu_wf_at(entry.prc_mp, entry.cpu_arr, cpu_id); process_thread_wf_thread_at(entry.prc_mp, entry.thrd_mp, thrd_ptr);
        unmap_pci_bar_4k_hide_step_from_k(&entry, kernel_k_to_kernel_u(locked), kernel_k_to_kernel_u(hidden), cpu_id, prc_ptr, thrd_ptr, pagetable, va, addr);
        unmap_pci_bar_4k_trace_hide_step(&hide_steps_snap, old(steps).view(), kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(hidden), cpu_id, va);
        unmap_pci_bar_4k_tlb_flush_steps_from_k(&flush_steps_snap, hidden_steps, &flush_entry, &flush_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, va);
        unmap_pci_bar_4k_flushed_step_from_k(&flushed_snap, &flushed_pre, &flushed_k, &flushed_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, va);
        let exit_k = *krnl;
        let f = pci_bar_function_of_page(entry.pci_bars.view(), addr)->0;
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thrd_ptr);
        process_thread_wf_thread_at(exit_start.prc_mp, exit_start.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(exit_start.prc_mp, exit_start.pt_mp, prc_ptr);
        kernel_pci_bar_unmapped_implies_u_step(&exit_start, &removed, pagetable, va, f, PageSize::SZ4k);
        process_cpu_wf_at(removed.prc_mp, removed.cpu_arr, cpu_id);
        kernel_cpu_thread_pagetable_lock_states_and_progress_changed_implies_u_step(&removed, &exit_k, &removed_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable);
        unmap_pci_bar_4k_exit_step_from_k(&exit_start, &removed_lctx, kernel_k_to_kernel_u(removed), kernel_k_to_kernel_u(exit_k), cpu_id, prc_ptr, thrd_ptr, pagetable, va, f);
        unmap_pci_bar_4k_trace_exit_steps(&*steps, flushed_steps, exit_steps, kernel_k_to_kernel_u(flushed_snap), kernel_k_to_kernel_u(flushed_k),
            kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, va, f);
    }
}
} // verus!
