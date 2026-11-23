use vstd::prelude::*;
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_pci_bar_map_2m_trace::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::map_io_leaf::install_io_2m_mapping;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::map_io_leaf::install_io_2m_mapping;

verus! {
/// With the directories of `va` installed, its 2M window held through `window_perm`, and cpu `cpu_id`, its running thread, and the
/// pagetable `pagetable` of the thread's process write-held: installs the IO 2M leaf mapping the slot's chunk `addr` for the function of
/// the array entry `owner_index`, releases the window, the progress, and every lock, and records the exit step that completes the trace
/// started at the projection of `entry`.
pub(super) fn map_pci_bar_2m_install_and_exit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, slot: usize, index: usize, va: VAddr,
    addr: PAddr, owner_index: usize, prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, Ghost(entry): Ghost<KernelK>,
    Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>, Tracked(pagetable_perm): Tracked<LockPerm>, Tracked(window_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        map_pci_bar_2m_trace_after_range(old(steps).view(), cpu_id, slot, index, va),
        old(steps).view()[0].old_u == kernel_k_to_kernel_u(entry),
        entry.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        entry.thrd_mp.dom().contains(thrd_ptr),
        entry.thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        slot < entry.pci_bars.view().len(),
        entry.pci_bars.view()[slot as int].spec_chunk_2m(index) == Some(addr),
        old(krnl).pci_bars == entry.pci_bars,
        va_2m_valid(va),
        pci_bar_2m_chunk_of(old(krnl).pci_bars.view(), addr, entry.pci_bars.view()[slot as int].bdf),
        io_page_range_valid(addr, PAGE_SZ_2M),
        owner_index < PCI_FUNCTIONS_PER_PROCESS,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(owner_index as int).used,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(owner_index as int).bdf == entry.pci_bars.view()[slot as int].bdf,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.state() is WriteLock,
        cpu_perm.thread_id() == old(lctx).thread_id(),
        cpu_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view().exited.view(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is Some,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0 is MapPciBar2m,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->MapPciBar2m_va == va,
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable,
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.no_hidden_user_l4_l3_entries(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).l1_table is None,
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable && w == window_of(va)),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        window_perm.state() is WriteLock,
        window_perm.thread_id() == old(lctx).thread_id(),
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va)),
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
        map_pci_bar_2m_syscall_trace(final(steps).view(), cpu_id, slot, index, va),
{
    let ghost dir_steps = steps.view();
    let ghost exit_start = *krnl;
    let ghost exit_lctx = *lctx;
    let indices = va2index(va);
    proof {
        assert(spec_va_4k_valid(va)) by (bit_vector) requires spec_va_2m_valid(va);
        spec_va_4k_valid_index_roundtrip(va);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    let l2_ptr = {
        proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
        let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_perm));
        let l4 = pt.higher.get_entry_l4(indices.0).unwrap();
        let l3 = pt.higher.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        l3.addr
    };
    let leaf = MapEntry { is_io: true, addr, write: true, execute_disable: true, present: true, owning_container: Ghost(ctn_ptr) };
    install_io_2m_mapping(krnl, pagetable, va, owner_index, l2_ptr, &leaf, Tracked(&mut *lctx), Tracked(&pagetable_perm), Tracked(&window_perm));
    let ghost installed = *krnl;
    let ghost installed_lctx = *lctx;
    proof {
        assert(va < 0x1_0000_0000_0000usize) by (bit_vector) requires va & (!0x0000_ffff_ffff_f000u64) as usize == 0;
    }
    let range = VaRange4K::new(va, 1);
    let tracked mut window_perms = Map::<WindowVa, LockPerm>::tracked_empty();
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
        window_perms.tracked_insert(window_of(va), window_perm);
        assert(range.view()[0] == va && va_range_2m_windows(range).contains(window_of(va))) by { range.wf_implies_view_index_is_start_plus_offset(); };
    }
    krnl.unlock_pagetable_range_windows::<true>(pagetable, &range, Tracked(&pagetable_perm), Tracked(&mut *lctx), Tracked(window_perms));
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_perm));
    proof { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); }
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        let exit_k = *krnl;
        let f = entry.pci_bars.view()[slot as int].bdf;
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thrd_ptr);
        process_pagetable_wf_process_at(exit_start.prc_mp, exit_start.pt_mp, prc_ptr);
        kernel_pci_bar_mapped_implies_u_step(&exit_start, &installed, pagetable, va, f, PageSize::SZ2m);
        process_cpu_wf_at(installed.prc_mp, installed.cpu_arr, cpu_id);
        kernel_cpu_thread_pagetable_window_lock_states_and_progress_changed_implies_u_step(&installed, &exit_k, &installed_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable);
        map_pci_bar_2m_exit_step_from_k(&exit_start, &exit_lctx, kernel_k_to_kernel_u(installed), kernel_k_to_kernel_u(exit_k), cpu_id, prc_ptr, thrd_ptr, pagetable, va, f, leaf);
        map_pci_bar_2m_trace_exit_step(&*steps, dir_steps, &entry, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, thrd_ptr, ctn_ptr, slot, index, va,
            addr, f, leaf);
    }
}
} // verus!
