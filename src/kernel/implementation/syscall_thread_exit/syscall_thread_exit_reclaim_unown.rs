use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_spec::thread_exit_detach_process_functions_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_thread_exit_reclaim_eof::thread_exit_detach_process_functions_eof;

verus! {
/// Give up the PCI functions of the running last thread's process once its page table maps nothing and is flushed, before
/// its held leaves are reclaimed. A process
/// with functions write-locks the root table and then its IOMMU table, if any, detaches that table from every function of
/// the array, releases every function, and unlocks the root table; a process without functions never takes the root-table
/// lock and only write-locks its IOMMU table, if any, which has no DID. A change of the user view is one unown step of the
/// partial trace that starts at `start`.
pub(super) fn thread_exit_reclaim_unown(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, Ghost(ctn_ptr): Ghost<RwLockContainerPtr>,
    Ghost(prc_ptr): Ghost<RwLockProcessPtr>, Ghost(thrd_ptr): Ghost<RwLockThreadPtr>, pagetable: RwLockPageTableRoot, iommu_table: Option<RwLockPageTableRoot>,
    Ghost(entry_lctx): Ghost<LocalContext>, Ghost(pt_entry): Ghost<TypedHeldLock>, Ghost(table_lctx): Ghost<LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
) -> (ret: (Tracked<Option<LockPerm>>, Ghost<TypedHeldLock>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_inserted(&entry_lctx, &table_lctx, KernelObjId::PageTable(pagetable), pt_entry),
        pt_entry.mode == TypedLockMode::Write,
        typed_lock_maps_unchanged(&table_lctx, old(lctx)),
        old(lctx).cpu_id() == cpu_id,
        index_valid(NUM_CPUS, cpu_id),
        entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
        entry_lctx.container_lock_map().dom() =~= set![ctn_ptr],
        entry_lctx.process_lock_map().dom() =~= set![prc_ptr],
        entry_lctx.thread_lock_map().dom() =~= set![thrd_ptr],
        entry_lctx.page_lock_map().dom().is_empty(),
        entry_lctx.scheduler_lock_map().dom().is_empty(),
        entry_lctx.cpu_set_lock_map().dom().is_empty(),
        entry_lctx.pagetable_lock_map().dom().is_empty(),
        entry_lctx.pagetable_window_lock_map().dom().is_empty(),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ4k),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ2m),
        entry_lctx.holds_no_allocator_locks(PageSize::SZ1g),
        entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
        entry_lctx.iommu_table_lock_map().dom().is_empty(),
        entry_lctx.iommu_root_table_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.container_lock_map(), ctn_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), prc_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(prc_ptr).view().iommu_table == iommu_table,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitReclaim { flushed: true }),
        old(krnl).pt_mp.dom().contains(pagetable),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom() =~= Set::<VAddr>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty(),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == cpu_id,
        final(lctx).thread_id() == old(lctx).thread_id(),
        ret.1.view().mode == TypedLockMode::Write,
        (ret.0.view() is Some) == (iommu_table is Some),
        iommu_table is Some ==> typed_lock_maps_inserted(&table_lctx, final(lctx), KernelObjId::IommuTable(iommu_table->Some_0), ret.1.view()),
        iommu_table is None ==> typed_lock_maps_unchanged(&table_lctx, final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 1,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        {
            let post_container = final(krnl).ctn_mp.spec_index(ctn_ptr);
            let pre_container = old(krnl).ctn_mp.spec_index(ctn_ptr);
            &&& post_container.view() == pre_container.view()
            &&& post_container.view_rodata() == pre_container.view_rodata()
            &&& post_container.locking_thread() == pre_container.locking_thread()
            &&& post_container.control() == pre_container.control()
        },
        final(krnl).prc_mp.dom().contains(prc_ptr),
        ({
            let post_process = final(krnl).prc_mp.spec_index(prc_ptr);
            let pre_process = old(krnl).prc_mp.spec_index(prc_ptr);
            &&& post_process.view() == pre_process.view()
            &&& post_process.view_rodata() == pre_process.view_rodata()
            &&& post_process.locking_thread() == pre_process.locking_thread()
            &&& post_process.control() == pre_process.control()
        }),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.spec_index(pagetable).view().higher
            == (PageTableHigher { pci: final(krnl).pt_mp.spec_index(pagetable).view().higher.pci, ..old(krnl).pt_mp.spec_index(pagetable).view().higher }),
        final(krnl).pt_mp.spec_index(pagetable).view().higher.pci.view() == Map::<PciBdf, Set<PciBarMapping>>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower,
        forall|l4i: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i),
        forall|l4i: L4Index, l3i: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_1g_l3(l4i, l3i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i)
                == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(l4i, l3i, l2i),
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i)
                == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(l4i, l3i, l2i, l1i),
        iommu_table matches Some(it) ==> {
            let table = final(krnl).it_mp.spec_index(it);
            &&& final(krnl).it_mp.dom().contains(it)
            &&& table.view().leaves_present()
            &&& table.view().proc_ptr == prc_ptr
            &&& table.view().did is None
            &&& ret.0.view()->Some_0.state() is WriteLock
            &&& ret.0.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& ret.0.view()->Some_0.lock_id() == table.locking_thread()->Write_lock_id
        },
{
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        if iommu_table is Some { process_iommu_table_wf_process_at(krnl.prc_mp, krnl.it_mp, prc_ptr); }
    }
    let ghost unown_k = *krnl;
    let ghost unown_lctx = *lctx;
    let ghost unown_before = steps.view();
    let ghost mut detached_irt = krnl.irt.view();
    let empty = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm)).higher.pci.is_empty();
    let iommu_table_lock_perm = if !empty {
        let Tracked(irt_lock_perm) = krnl.wlock_iommu_root_table(Tracked(&mut *lctx));
        let perm = match iommu_table {
            Some(it) => {
                let Tracked(perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
                let ghost locked_k = *krnl;
                iommu_root_table_detach_array(&mut krnl.irt, &mut krnl.iommu_tlb, &mut krnl.it_mp, it,
                    &krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm)).higher.pci, Ghost(locked_k), Tracked(&*lctx),
                    Tracked(&irt_lock_perm), Tracked(&perm));
                proof {
                    // The DID's anchor is a function of the array, so nothing may stay cached for that DID.
                    if let Some(did) = locked_k.it_mp.spec_index(it).view().did {
                        assert(krnl.iommu_tlb.spec_index(did) == (SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }) && krnl.iommu_tlb.structure_cache(did).is_empty()) by {
                            iommu_root_table_process_wf_table_at(locked_k.irt.view(), locked_k.prc_mp, locked_k.it_mp, it);
                            assert(pci_bdf_valid(pci_bdf_of_did(did).0, pci_bdf_of_did(did).1, pci_bdf_of_did(did).2)) by (nonlinear_arith) requires vtd_domain_id_valid(did);
                            pci_function_ownership_wf_function_at(locked_k.irt.view(), locked_k.prc_mp, locked_k.pt_mp, pci_bdf_of_did(did).0, pci_bdf_of_did(did).1, pci_bdf_of_did(did).2);
                            assert(krnl.iommu_tlb.spec_index(did).tlb_4k =~= Map::empty() && krnl.iommu_tlb.spec_index(did).tlb_2m =~= Map::empty() && krnl.iommu_tlb.spec_index(did).tlb_1g =~= Map::empty());
                        };
                    }
                    assert(thread_exit_detach_process_functions_eof_transition_framing(locked_k, *krnl, pagetable, it)) by { reveal(thread_exit_detach_process_functions_eof_transition_framing); };
                    thread_exit_detach_process_functions_eof(locked_k, *krnl, prc_ptr, pagetable, it);
                    detached_irt = krnl.irt.view();
                }
                krnl.release_pci_functions(pagetable, Tracked(&*lctx), Tracked(pagetable_lock_perm), Tracked(&irt_lock_perm));
                Tracked(Some(perm))
            },
            None => {
                krnl.release_pci_functions(pagetable, Tracked(&*lctx), Tracked(pagetable_lock_perm), Tracked(&irt_lock_perm));
                Tracked(None)
            },
        };
        krnl.wunlock_iommu_root_table(Tracked(&mut *lctx), Tracked(irt_lock_perm));
        proof { assert(lctx.iommu_root_table_lock_map() =~= unown_lctx.iommu_root_table_lock_map()); }
        perm
    } else {
        match iommu_table {
            Some(it) => {
                let Tracked(perm) = krnl.wlock_iommu_table(it, Tracked(&mut *lctx));
                Tracked(Some(perm))
            },
            None => Tracked(None),
        }
    };
    let ghost it_entry = TypedHeldLock { lock_id: krnl.it_mp.lock_id_by_key(iommu_table->Some_0), mode: TypedLockMode::Write };
    proof {
        let unowned_k = *krnl;
        let unowned_lctx = *lctx;
        if empty { assert(krnl.pt_mp.spec_index(pagetable).view().higher.pci.view() =~= Map::<PciBdf, Set<PciBarMapping>>::empty()); }
        if let Some(it) = iommu_table {
            iommu_table_perms_wf_at(krnl.it_mp, it);
            // A table without functions has no DID: a DID's anchor is a function of its owner's array.
            if empty {
                iommu_root_table_process_wf_table_at(unown_k.irt.view(), unown_k.prc_mp, unown_k.it_mp, it);
                if let Some(did) = unown_k.it_mp.spec_index(it).view().did {
                    assert(pci_bdf_valid(pci_bdf_of_did(did).0, pci_bdf_of_did(did).1, pci_bdf_of_did(did).2)) by (nonlinear_arith) requires vtd_domain_id_valid(did);
                    pci_function_ownership_wf_function_at(unown_k.irt.view(), unown_k.prc_mp, unown_k.pt_mp, pci_bdf_of_did(did).0, pci_bdf_of_did(did).1, pci_bdf_of_did(did).2);
                }
            }
        }
        if iommu_table is Some || !empty {
            thread_exit_unown_step_from_k(&unown_k, &unowned_k, &unown_lctx, &unowned_lctx, cpu_id, ctn_ptr, prc_ptr, thrd_ptr, pagetable, iommu_table, detached_irt);
            if lctx.kernel_view_locking_state() is Acquire { enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx); }
            assert(lctx.pagetable_lock_map().dom().contains(pagetable));
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
            thread_exit_trace_push(&*steps, unown_before, start, pre, kernel_k_to_kernel_u(unown_k), kernel_k_to_kernel_u(unowned_k), cpu_id);
        }
    }
    (iommu_table_lock_perm, Ghost(it_entry))
}
} // verus!
