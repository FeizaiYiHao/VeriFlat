use vstd::prelude::*;
use crate::*;
use super::unmap_4k_mapped_page_ptr::unmap_4k_leaf_table_ptrs;
#[cfg(verus_keep_ghost)]
use super::unmap_io_leaf_eof::*;

verus! {
/// The entry of the PCI function array of the write-held `pagetable` that holds the function owning the BAR page or 2M chunk
/// `addr` of the IO leaf of `pagetable` at `m`, which the array records.
fn io_leaf_function_entry(krnl: &KernelK, pagetable: RwLockPageTableRoot, addr: PAddr, Ghost(m): Ghost<PciBarMapping>, Tracked(lctx): Tracked<&LocalContext>,
    pagetable_perm: Tracked<&LockPerm>) -> (ret: usize)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == lctx.thread_id(),
        pagetable_perm.view().lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        pci_bar_function_of_page(krnl.pci_bars.view(), addr) is Some,
        krnl.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(pci_bar_function_of_page(krnl.pci_bars.view(), addr)->0),
        krnl.pt_mp.spec_index(pagetable).view().higher.pci.view()[pci_bar_function_of_page(krnl.pci_bars.view(), addr)->0].contains(m),
    ensures
        ret < PCI_FUNCTIONS_PER_PROCESS,
        krnl.pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(ret as int).used,
        krnl.pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(ret as int).bdf == pci_bar_function_of_page(krnl.pci_bars.view(), addr)->0,
{
    let ghost f = pci_bar_function_of_page(krnl.pci_bars.view(), addr)->0;
    let (bus, device, function) = krnl.pci_bars.function_of_page(addr).unwrap();
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); };
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), pagetable_perm);
    let index = pt.higher.pci.find(bus, device, function).unwrap();
    proof { pt.higher.pci.wf_function_at(f); }
    index
}

/// Clear the non-empty, unresolvable IO 4K leaf `va` of the write-held `pagetable`, which lists no CPU stale and whose PCI functions
/// were released; the page array is not touched.
pub fn remove_nonempty_io_4k_mapping(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_nonempty_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_nonempty_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.perm.is_io,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)), held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)), held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.higher == old_c.higher && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_nonempty_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_nonempty_l2(l4i, l3i, l2i) == old_c.spec_nonempty_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_nonempty_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_nonempty_2m_l2(l4i, l3i, l2i) == old_c.spec_nonempty_2m_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
                    ==> new_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)
            &&& new_c.spec_nonempty_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None
        }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    let indices = va2index(va);
    proof {
        spec_va_4k_valid_index_roundtrip(va); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
    }
    pagetable_map_clear_nonempty_4k_leaf(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, indices, Tracked(&mut *lctx), pagetable_perm);
    proof {
        assert(remove_nonempty_io_4k_mapping_eof_transition_framing(*old(krnl), *krnl, pagetable, va)) by { reveal(remove_nonempty_io_4k_mapping_eof_transition_framing); };
        remove_nonempty_io_4k_mapping_eof(*old(krnl), *krnl, pagetable, va);
    }
}

/// Clear the non-empty, unresolvable IO 2M leaf `va` of the write-held `pagetable`, which lists no CPU stale and whose PCI functions
/// were released; the page array is not touched.
pub fn remove_nonempty_io_2m_mapping(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_nonempty_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_nonempty_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.perm.is_io,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)), held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)), held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.higher == old_c.higher && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.l2_perms.dom() == old_c.lower.l2_perms.dom() && new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)]
                (p, i) != (old_c.spec_nonempty_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
            &&& new_c.lower.l2_entry(old_c.spec_nonempty_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va)).is_empty()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_nonempty_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_nonempty_l2(l4i, l3i, l2i) == old_c.spec_nonempty_l2(l4i, l3i, l2i)
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_nonempty_2m_l2(l4i, l3i, l2i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
                    ==> new_c.spec_nonempty_2m_l2(l4i, l3i, l2i) == old_c.spec_nonempty_2m_l2(l4i, l3i, l2i)
            &&& new_c.spec_nonempty_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
            &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)]
                old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)
        }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    proof { held_kernel_objects_unchanged_reflexive(&*krnl, &*lctx); }
    let indices = va2index(va);
    proof {
        spec_va_2m_valid_index_roundtrip(va); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_2m_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
    }
    pagetable_map_clear_nonempty_2m_leaf(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), Tracked(&mut *lctx), pagetable_perm);
    proof {
        assert(remove_nonempty_io_2m_mapping_eof_transition_framing(*old(krnl), *krnl, pagetable, va)) by { reveal(remove_nonempty_io_2m_mapping_eof_transition_framing); };
        remove_nonempty_io_2m_mapping_eof(*old(krnl), *krnl, pagetable, va);
    }
}

/// Remove the hidden IO 4K leaf `va`, which maps `addr`, of the write-held `pagetable` after its stale TLB entries are flushed, and
/// drop its BAR mapping `(va, 4K)` from the function owning `addr`; the caller holds the leaf's window, and no CPU is listed stale
/// for it. The page array is not touched.
pub fn remove_io_4k_mapping(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, addr: PAddr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>,
    Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).is_io,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).addr == addr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
    ensures
        (forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l4(l4i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some)
            ==> forall|l4i: L4Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l4(l4i)]
                final(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l4(l4i) is Some
                    ==> final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some,
        (forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l3(l4i, l3i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l3(l4i, l3i) is Some)
            ==> forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l3(l4i, l3i)]
                final(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l3(l4i, l3i) is Some
                    ==> final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l3(l4i, l3i) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows()
            ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        pci_bar_function_of_page(old(krnl).pci_bars.view(), addr) is Some,
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            let f = pci_bar_function_of_page(old(krnl).pci_bars.view(), addr)->0;
            &&& old_c.higher.pci.view().dom().contains(f) && old_c.higher.pci.view()[f].contains((va, PageSize::SZ4k))
            &&& new_c.higher == (PageTableHigher { pci: new_c.higher.pci, ..old_c.higher })
            &&& new_c.higher.pci.mapping_counts() == old_c.higher.pci.mapping_counts().insert(f, (old_c.higher.pci.mapping_counts()[f] - 1) as nat)
            &&& new_c.mapping_4k() == old_c.mapping_4k().remove(va) && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g()
            &&& new_c.page_closure() == old_c.page_closure()
            &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_page(p).entry_lock(i).l1()]
                pei_valid(i) && !old_c.lower.l2_entry_hides_l1(p, i) ==> !new_c.lower.l2_entry_hides_l1(p, i)
        }),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    let indices = va2index(va);
    assert(spec_index2va(indices) == va) by { spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3); };
    proof {
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c.wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        c.spec_resolve_mapping_4k_l1_some_implies_spec_nonempty_4k_l1_eq(indices.0, indices.1, indices.2, indices.3);
        pagetable_pci_mappings_wf_present_4k_at(krnl.pci_bars.view(), krnl.pt_mp, krnl.pt_lower.view(), pagetable, va);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
        assert(spec_v2l4index(window_of(va).va) == indices.0 && spec_v2l3index(window_of(va).va) == indices.1 && spec_v2l2index(window_of(va).va) == indices.2) by {
            broadcast use spec_va_2m_valid_index_roundtrip; spec_index2va_injective();
        };
    }
    let index = io_leaf_function_entry(krnl, pagetable, addr, Ghost((va, PageSize::SZ4k)), Tracked(&*lctx), pagetable_perm);
    let (l2_ptr, l1_ptr) = unmap_4k_leaf_table_ptrs(krnl, pagetable, va, indices, Tracked(&*lctx), pagetable_perm);
    proof { old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable); }
    pagetable_map_unmap_4k_kernel(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, indices, l2_ptr, l1_ptr, Tracked(window_perm), Tracked(&mut *lctx), pagetable_perm);
    pagetable_map_update_pci_mapping(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, index, Ghost((va, PageSize::SZ4k)), false, Tracked(&*lctx), pagetable_perm);
    proof {
        let f = pci_bar_function_of_page(old(krnl).pci_bars.view(), addr)->0;
        assert(remove_io_4k_mapping_eof_transition_framing(*old(krnl), *krnl, pagetable, va, f)) by { reveal(remove_io_4k_mapping_eof_transition_framing); };
        remove_io_4k_mapping_eof(*old(krnl), *krnl, pagetable, va, f);
    }
}

/// Remove the hidden IO 2M leaf `va`, which maps the chunk `addr`, of the write-held `pagetable` after its stale TLB entries are
/// flushed, and drop its BAR mapping `(va, 2M)` from the function owning `addr`; the caller holds the leaf's window, whose L2 page
/// is `l2_ptr`, and no CPU is listed stale for it. The page array is not touched.
pub fn remove_io_2m_mapping(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, addr: PAddr, l2_ptr: PageMapPtr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>,
    Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).is_io,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).addr == addr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
    ensures
        (forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l4(l4i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some)
            ==> forall|l4i: L4Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l4(l4i)]
                final(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l4(l4i) is Some
                    ==> final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some,
        (forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l3(l4i, l3i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l3(l4i, l3i) is Some)
            ==> forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l3(l4i, l3i)]
                final(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_nonempty_l3(l4i, l3i) is Some
                    ==> final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l3(l4i, l3i) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows()
            ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        pci_bar_function_of_page(old(krnl).pci_bars.view(), addr) is Some,
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            let f = pci_bar_function_of_page(old(krnl).pci_bars.view(), addr)->0;
            &&& old_c.higher.pci.view().dom().contains(f) && old_c.higher.pci.view()[f].contains((va, PageSize::SZ2m))
            &&& new_c.higher == (PageTableHigher { pci: new_c.higher.pci, ..old_c.higher })
            &&& new_c.higher.pci.mapping_counts() == old_c.higher.pci.mapping_counts().insert(f, (old_c.higher.pci.mapping_counts()[f] - 1) as nat)
            &&& new_c.mapping_2m() == old_c.mapping_2m().remove(va) && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_1g() == old_c.mapping_1g()
            &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_page(p).entry_lock(i).l1()]
                pei_valid(i) && !old_c.lower.l2_entry_hides_l1(p, i) ==> !new_c.lower.l2_entry_hides_l1(p, i)
        }),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
{
    let indices = va2index(va);
    proof {
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        assert(indices.0 == spec_v2l4index(va) && indices.1 == spec_v2l3index(va) && indices.2 == spec_v2l2index(va) && window_of(va).va == va) by {
            broadcast use spec_va_2m_valid_index_roundtrip;
        };
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c.wf_mapping_2m_at(indices.0, indices.1, indices.2);
        c.spec_resolve_mapping_2m_l2_some_implies_spec_nonempty_2m_l2_eq(indices.0, indices.1, indices.2);
        pagetable_pci_mappings_wf_present_2m_at(krnl.pci_bars.view(), krnl.pt_mp, krnl.pt_lower.view(), pagetable, va);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
    }
    let index = io_leaf_function_entry(krnl, pagetable, addr, Ghost((va, PageSize::SZ2m)), Tracked(&*lctx), pagetable_perm);
    proof { old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable); }
    pagetable_map_unmap_2m_kernel(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), l2_ptr, Tracked(window_perm), Tracked(&mut *lctx),
        pagetable_perm);
    pagetable_map_update_pci_mapping(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, index, Ghost((va, PageSize::SZ2m)), false, Tracked(&*lctx), pagetable_perm);
    proof {
        let f = pci_bar_function_of_page(old(krnl).pci_bars.view(), addr)->0;
        assert(remove_io_2m_mapping_eof_transition_framing(*old(krnl), *krnl, pagetable, va, l2_ptr, f)) by { reveal(remove_io_2m_mapping_eof_transition_framing); };
        remove_io_2m_mapping_eof(*old(krnl), *krnl, pagetable, va, l2_ptr, f);
    }
}
}
