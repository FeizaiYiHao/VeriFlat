use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::map_io_leaf_eof::*;

verus! {
/// Install the present IO 4K leaf `entry` at `va` in the write-held `pagetable`, whose 2M window this thread holds and whose L2 and
/// L1 pages on the path to `va` are `l2_ptr` and `l1_ptr`, and record the BAR mapping `(va, 4K)` under the function of the used
/// entry `index` of the table's PCI function array, which owns the BAR page `entry.addr`. The page array is not touched.
pub fn install_io_4k_mapping(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, index: usize, l2_ptr: PageMapPtr, l1_ptr: PageMapPtr, entry: &MapEntry,
    Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == l1_ptr,
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        entry.is_io,
        entry.present,
        mapping_4k_target_valid(entry.addr, entry.is_io),
        index < PCI_FUNCTIONS_PER_PROCESS,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(index as int).used,
        pci_bar_function_of_page(old(krnl).pci_bars.view(), entry.addr) == Some(old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(index as int).bdf),
    ensures
        (forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some)
            ==> forall|l4i: L4Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i)]
                final(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i) is Some
                    ==> final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some,
        (forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l3(l4i, l3i) is Some)
            ==> forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i)]
                final(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i) is Some
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
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            let f = old_c.higher.pci.spec_entry(index as int).bdf;
            &&& old_c.higher.pci.view().dom().contains(f) && !old_c.higher.pci.view()[f].contains((va, PageSize::SZ4k))
            &&& new_c.higher == (PageTableHigher { pci: new_c.higher.pci, ..old_c.higher })
            &&& new_c.higher.pci.view() == old_c.higher.pci.view().insert(f, old_c.higher.pci.view()[f].insert((va, PageSize::SZ4k)))
            &&& new_c.higher.pci.view().dom() == old_c.higher.pci.view().dom()
            &&& new_c.higher.pci.mapping_counts() == old_c.higher.pci.mapping_counts().insert(f, (old_c.higher.pci.mapping_counts()[f] + 1) as nat)
            &&& new_c.mapping_4k() == old_c.mapping_4k().insert(va, *entry) && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g()
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
    let ghost f = krnl.pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(index as int).bdf;
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable).inv() && spec_index2va(indices) == va) by {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
    };
    proof {
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c.higher.pci.wf_entry_at(index as int);
        c.wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        c.spec_resolve_mapping_l2_some_implies_spec_held_l2_eq(indices.0, indices.1, indices.2);
        c.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(indices.0, indices.1);
        pagetable_pci_mappings_wf_mapping_at(krnl.pci_bars.view(), krnl.pt_mp, krnl.pt_lower.view(), pagetable, f, (va, PageSize::SZ4k));
        pci_function_mapping_count_lt_usize_max(krnl.pt_mp, krnl.pt_lower.view(), krnl.pci_bars.view(), pagetable, f);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
        assert(spec_v2l4index(window_of(va).va) == indices.0 && spec_v2l3index(window_of(va).va) == indices.1 && spec_v2l2index(window_of(va).va) == indices.2) by {
            broadcast use spec_va_2m_valid_index_roundtrip; spec_index2va_injective();
        };
        old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
    }
    pagetable_map_insert_4k_wlocked(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, indices, l2_ptr, l1_ptr, entry, Tracked(window_perm), Tracked(&mut *lctx), pagetable_perm);
    let ghost mid = *krnl;
    pagetable_map_update_pci_mapping(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, index, Ghost((va, PageSize::SZ4k)), true, Tracked(&*lctx), pagetable_perm);
    proof {
        assert(install_io_4k_mapping_eof_transition_framing(*old(krnl), mid, *krnl, pagetable, va, f, *entry)) by { reveal(install_io_4k_mapping_eof_transition_framing); };
        install_io_4k_mapping_eof(*old(krnl), mid, *krnl, pagetable, va, f, *entry);
    }
}

/// Install the present IO 2M leaf `entry` at `va` in the write-held `pagetable`, whose 2M window this thread holds and whose L2 page
/// on the path to `va` is `l2_ptr`, and record the BAR mapping `(va, 2M)` under the function of the used entry `index` of the
/// table's PCI function array, which owns the 2M chunk `entry.addr`. The window links no L1 page and lists no stale CPU. The page array
/// is not touched.
pub fn install_io_2m_mapping(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, index: usize, l2_ptr: PageMapPtr, entry: &MapEntry, Tracked(lctx): Tracked<&mut LocalContext>,
    pagetable_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_v2l4index(va),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).l1_table is None,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is None,
        !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        entry.is_io,
        entry.present,
        mapping_2m_target_valid(entry.addr, entry.is_io),
        index < PCI_FUNCTIONS_PER_PROCESS,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(index as int).used,
        pci_bar_2m_chunk_of(old(krnl).pci_bars.view(), entry.addr, old(krnl).pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(index as int).bdf),
    ensures
        (forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some)
            ==> forall|l4i: L4Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i)]
                final(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l4(l4i) is Some
                    ==> final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l4(l4i) is Some,
        (forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().higher.spec_resolve_mapping_l3(l4i, l3i) is Some)
            ==> forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i)]
                final(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable).view().higher.spec_held_l3(l4i, l3i) is Some
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
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            let f = old_c.higher.pci.spec_entry(index as int).bdf;
            &&& old_c.higher.pci.view().dom().contains(f) && !old_c.higher.pci.view()[f].contains((va, PageSize::SZ2m))
            &&& new_c.higher == (PageTableHigher { pci: new_c.higher.pci, ..old_c.higher })
            &&& new_c.higher.pci.view() == old_c.higher.pci.view().insert(f, old_c.higher.pci.view()[f].insert((va, PageSize::SZ2m)))
            &&& new_c.higher.pci.view().dom() == old_c.higher.pci.view().dom()
            &&& new_c.higher.pci.mapping_counts() == old_c.higher.pci.mapping_counts().insert(f, (old_c.higher.pci.mapping_counts()[f] + 1) as nat)
            &&& new_c.mapping_2m() == old_c.mapping_2m().insert(va, *entry) && new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_1g() == old_c.mapping_1g()
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
    let ghost f = krnl.pt_mp.spec_index(pagetable).view().higher.pci.spec_entry(index as int).bdf;
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); };
    proof {
        let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        assert(indices.0 == spec_v2l4index(va) && indices.1 == spec_v2l3index(va) && indices.2 == spec_v2l2index(va) && window_of(va).va == va) by {
            broadcast use spec_va_2m_valid_index_roundtrip;
        };
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        c.higher.pci.wf_entry_at(index as int);
        c.higher.wf_l4_at(indices.0);
        c.l3_links_l2_wf_at(c.spec_resolve_mapping_l4(indices.0)->0.addr, indices.1);
        c.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(indices.0, indices.1);
        c.wf_l2_at(c.window_l2_page(indices.0, indices.1), indices.2);
        c.wf_mapping_2m_at(indices.0, indices.1, indices.2);
        pagetable_pci_mappings_wf_mapping_at(krnl.pci_bars.view(), krnl.pt_mp, krnl.pt_lower.view(), pagetable, f, (va, PageSize::SZ2m));
        pci_function_mapping_count_lt_usize_max(krnl.pt_mp, krnl.pt_lower.view(), krnl.pci_bars.view(), pagetable, f);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
        assert(!c.page_closure().contains(entry.addr)) by {
            let bars = krnl.pci_bars.view();
            if c.page_closure().contains(entry.addr) {
                pagetable_pages_wf_closure_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, entry.addr);
                page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
                pci_bar_pages_unavailable_wf_at(bars, krnl.pg_arr, page_ptr2page_index(entry.addr));
            }
        };
        old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
    }
    pagetable_map_insert_2m_wlocked(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), l2_ptr, entry, Tracked(window_perm), Tracked(&mut *lctx),
        pagetable_perm);
    let ghost mid = *krnl;
    pagetable_map_update_pci_mapping(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, index, Ghost((va, PageSize::SZ2m)), true, Tracked(&*lctx), pagetable_perm);
    proof {
        assert(install_io_2m_mapping_eof_transition_framing(*old(krnl), mid, *krnl, pagetable, va, f, *entry)) by { reveal(install_io_2m_mapping_eof_transition_framing); };
        install_io_2m_mapping_eof(*old(krnl), mid, *krnl, pagetable, va, f, *entry);
    }
}
}
