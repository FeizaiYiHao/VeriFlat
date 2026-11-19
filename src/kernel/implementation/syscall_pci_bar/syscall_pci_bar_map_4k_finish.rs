use vstd::prelude::*;
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_pci_bar_map_4k_trace::*;
use super::syscall_pci_bar_map_4k_exit::map_pci_bar_4k_install_and_exit;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::{mmap_4k_build_structure::MissingPageTableLevel, mmap_4k_install_one::install_one_mmap_4k_directory_page};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::{mmap_4k_build_structure::MissingPageTableLevel, mmap_4k_install_one::install_one_mmap_4k_directory_page};

verus! {
/// With cpu `cpu_id`, its running thread, and the pagetable `pagetable` of the thread's process write-held since the entry snapshot
/// `entry_lctx` was aligned with, `va` uncovered, the slot's page `addr` of the function of the array entry `index`, and mmap's quota:
/// records the enter step, installs the missing L4, L3, and L2 directories with one step each, installs the IO leaf in the window of
/// `va`, releases every lock, and records the exit step.
pub(super) fn map_pci_bar_4k_map_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, slot: usize, page_index: usize, va: VAddr,
    addr: PAddr, index: usize, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot,
    Ghost(entry_lctx): Ghost<LocalContext>, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>, Tracked(pagetable_perm): Tracked<LockPerm>,
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
        map_pci_bar_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, slot, page_index, va) is Success,
        slot < old(krnl).pci_bars.view().len(),
        old(krnl).pci_bars.view()[slot as int].spec_page_4k(page_index) == Some(addr),
        pci_bar_function_of_page(old(krnl).pci_bars.view(), addr) == Some(old(krnl).pci_bars.view()[slot as int].bdf),
        io_page_range_valid(addr, PAGE_SZ_4K),
        index < PCI_FUNCTIONS_PER_PROCESS,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(index as int).used,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(index as int).bdf == old(krnl).pci_bars.view()[slot as int].bdf,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k >= 4,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        ({
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let idx = spec_va2index(va);
            &&& !table.mapping_1g().dom().contains(spec_index2va((idx.0, idx.1, 0, 0)))
            &&& !table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, idx.2, 0)))
            &&& !table.mapping_4k().dom().contains(va)
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
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
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
        old(krnl).pt_mp.spec_index(pagetable).view().higher.proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
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
        map_pci_bar_4k_syscall_trace(final(steps).view(), cpu_id, slot, page_index, va),
{
    let ghost entry = old(steps).snapshot_k();
    assert(!(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is Zombie)) by {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
    };
    let indices = va2index(va);
    proof {
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        spec_va_4k_index_roundtrip_at(window_of(va).va, indices.0, indices.1, indices.2, 0usize);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).higher.wf_mapping_1g_at(indices.0, indices.1);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_2m_at(indices.0, indices.1, indices.2);
        container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
        let (l4i, l3i, l2i) = (indices.0, indices.1, indices.2);
        assert(page_table_key_2m_valid::<PT_TYPE>(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
    }
    let alloc_ptr_4k = krnl.ctn_mp.borrow_rodata(ctn_ptr).borrow().allocator_ptr_4k;
    let (l4_present, l3_present, l2_present) = {
        let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_perm));
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
        match pt.higher.get_entry_l4(indices.0) {
            None => (false, false, false),
            Some(l4) => match pt.higher.get_entry_l3(indices.0, indices.1, &l4) {
                None => (true, false, false),
                Some(l3) => (true, true, pt.higher.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).is_some()),
            },
        }
    };
    // enter step: the three locks taken since the entry, the window of `va` when it exists, and the progress of mapping `va`
    let tracked mut held_window: Option<LockPerm> = None;
    if l3_present {
        proof { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
        let Tracked(w) = krnl.lock_pagetable_window::<true>(pagetable, indices.0, indices.1, indices.2, Tracked(&pagetable_perm), Tracked(&mut *lctx));
        proof { held_window = Some(w); }
    }
    let ghost locked = *krnl;
    let ghost locked_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::MapPciBar4k { va, directory: Mmap4kDirectory::None })), Tracked(&*lctx), Tracked(&thread_perm));
    proof {
        let entered = *krnl;
        let c = whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable);
        assert(entered.pt_lower.view() =~= entry.pt_lower.view().insert(pagetable, entered.pt_lower.view().spec_index(pagetable)));
        if !l3_present && c.lower.pagetable_window_locks.dom().contains(window_of(va)) { pagetable_lower_wf_at(entry.pt_mp, entry.pt_lower.view(), pagetable); c.wf_window_locks_va_at(window_of(va)); }
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        process_cpu_wf_at(entry.prc_mp, entry.cpu_arr, cpu_id); process_thread_wf_thread_at(entry.prc_mp, entry.thrd_mp, thrd_ptr);
        kernel_cpu_thread_pagetable_window_lock_states_and_progress_changed_implies_u_step(&entry, &entered, &entry_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable);
        map_pci_bar_4k_enter_step_from_u(&entry, kernel_k_to_kernel_u(entered), whole_pagetable(entered.pt_mp, entered.pt_lower.view(), pagetable).lower.pagetable_window_locks, cpu_id,
            prc_ptr, thrd_ptr, pagetable, slot, page_index, va);
        map_pci_bar_4k_trace_enter_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(entry), kernel_k_to_kernel_u(entered), cpu_id, slot, page_index, va);
    }
    // directory steps: the missing L4, L3, and L2 entries, in increasing rank
    if !l4_present {
        let ghost before = steps.view();
        proof {
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
            container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr);
        }
        let _ = install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L4, alloc_ptr_4k, thrd_ptr, prc_ptr, ctn_ptr, cpu_id, pagetable, (indices.0, indices.1, indices.2), indices.2,
            indices.2, true, None, thrd_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&thread_perm), Tracked(&thread_perm), Tracked(&pagetable_perm), Tracked(None), Tracked(None),
            Tracked(None));
        proof { map_pci_bar_4k_trace_directory_step(&*steps, before, cpu_id, slot, page_index, va); }
    }
    if !l3_present {
        let ghost before = steps.view();
        proof {
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).higher.wf_mapping_1g_at(indices.0, indices.1);
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
            container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr);
        }
        let Tracked(minted) = install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L3, alloc_ptr_4k, thrd_ptr, prc_ptr, ctn_ptr, cpu_id, pagetable,
            (indices.0, indices.1, indices.2), indices.2, indices.2, true, None, thrd_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&thread_perm), Tracked(&thread_perm),
            Tracked(&pagetable_perm), Tracked(None), Tracked(None), Tracked(None));
        proof {
            map_pci_bar_4k_trace_directory_step(&*steps, before, cpu_id, slot, page_index, va);
            let tracked mut minted = minted;
            held_window = Some(minted.tracked_remove(indices.2));
        }
    }
    let tracked window_perm = held_window.tracked_unwrap();
    if !l2_present {
        let ghost before = steps.view();
        proof {
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
            container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr);
        }
        let _ = install_one_mmap_4k_directory_page(krnl, MissingPageTableLevel::L2, alloc_ptr_4k, thrd_ptr, prc_ptr, ctn_ptr, cpu_id, pagetable, (indices.0, indices.1, indices.2), indices.2,
            indices.2, true, None, thrd_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&thread_perm), Tracked(&thread_perm), Tracked(&pagetable_perm), Tracked(None), Tracked(None),
            Tracked(Some(&window_perm)));
        proof { map_pci_bar_4k_trace_directory_step(&*steps, before, cpu_id, slot, page_index, va); }
    }
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip;
        process_perms_wf_at(krnl.prc_mp, prc_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
    }
    map_pci_bar_4k_install_and_exit(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, slot, page_index, va, addr, index, prc_ptr, thrd_ptr, ctn_ptr, pagetable, Ghost(entry),
        Tracked(cpu_perm), Tracked(thread_perm), Tracked(pagetable_perm), Tracked(window_perm));
}
} // verus!
