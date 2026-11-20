use vstd::prelude::*;
use crate::*;

verus! {
/// Installs the present IO 4K leaf `entry` at `va` in the write-held `pagetable` (from `pre` to `mid`, which keeps the big-lock
/// payload and resets its backup to the new window half) and then records the BAR mapping `(va, 4K)` under the function `f` (from
/// `mid` to `post`, which changes only the table's PCI function array); every other held entry, table, and kernel field, the page
/// array included, is unchanged.
#[verifier::opaque]
pub(super) open spec fn install_io_4k_mapping_eof_transition_framing(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let mid_c = whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    &&& mid == (KernelK { pt_mp: mid.pt_mp, pt_lower: mid.pt_lower, ..pre })
    &&& mid.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& mid.pt_lower.view() == pre.pt_lower.view().insert(pagetable, mid.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& mid.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& mid.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& mid_c.higher == old_c.higher
    &&& mid_c.mapping_4k() == old_c.mapping_4k().insert(va, entry) && mid_c.mapping_2m() == old_c.mapping_2m() && mid_c.mapping_1g() == old_c.mapping_1g()
    &&& mid_c.page_closure() == old_c.page_closure()
    &&& mid_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger mid_c.lower.l2_entry(p, i)] mid_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger mid_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> mid_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger mid_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
            ==> mid_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& mid_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some
    &&& mid_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.addr == entry.addr
    &&& mid_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.perm.is_io == entry.is_io
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger mid_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> mid_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& post == (KernelK { pt_mp: post.pt_mp, ..mid })
    &&& post.pt_mp.unchanged_except(&mid.pt_mp, pagetable)
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == mid.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == mid.pt_mp.spec_index(pagetable).being_killed()
    &&& new_c.higher == (PageTableHigher { pci: new_c.higher.pci, ..mid_c.higher })
    &&& new_c.mapping_4k() == mid_c.mapping_4k() && new_c.mapping_2m() == mid_c.mapping_2m() && new_c.mapping_1g() == mid_c.mapping_1g() && new_c.page_closure() == mid_c.page_closure()
    &&& new_c.lower == mid_c.lower
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)] new_c.spec_held_l2(l4i, l3i, l2i) == mid_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)] new_c.spec_held_2m_l2(l4i, l3i, l2i) == mid_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == mid_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id) == mid_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& new_c.kernel_l4_end() == mid_c.kernel_l4_end()
    &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_held_l4(l4i)] new_c.higher.spec_held_l4(l4i) == mid_c.higher.spec_held_l4(l4i)
    &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_resolve_mapping_l4(l4i)] new_c.higher.spec_resolve_mapping_l4(l4i) == mid_c.higher.spec_resolve_mapping_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_held_l3(l4i, l3i)] new_c.higher.spec_held_l3(l4i, l3i) == mid_c.higher.spec_held_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_l3(l4i, l3i)] new_c.higher.spec_resolve_mapping_l3(l4i, l3i) == mid_c.higher.spec_resolve_mapping_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_held_1g_l3(l4i, l3i)] new_c.higher.spec_held_1g_l3(l4i, l3i) == mid_c.higher.spec_held_1g_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)] new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i) == mid_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)
    &&& new_c.higher.pci.view() == mid_c.higher.pci.view().insert(f, mid_c.higher.pci.view()[f].insert((va, PageSize::SZ4k)))
    &&& new_c.higher.pci.view().dom() == old_c.higher.pci.view().dom()
    &&& forall|g: PciBdf, n: PciBarMapping| #![trigger new_c.higher.pci.view()[g].contains(n)] new_c.higher.pci.view().dom().contains(g)
        ==> new_c.higher.pci.view()[g].contains(n) == (old_c.higher.pci.view()[g].contains(n) || g == f && n == (va, PageSize::SZ4k))
}

/// The page-table relations close: the new leaf is an IO leaf no page lists, and the table's PCI function array, which owns `f`,
/// keeps its functions, so the table's process has not emptied its tables.
proof fn install_io_4k_mapping_eof_page_tables(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires
        pre.inv(),
        install_io_4k_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        entry.is_io,
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp),
{
    reveal(install_io_4k_mapping_eof_transition_framing);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid; reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_1g_valid_index_roundtrip, spec_index2va_2m_valid; reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp)) by { reveal(pci_function_ownership_wf); };
}

/// `pagetable_pci_mappings_wf`: the new record `(va, 4K)` of `f` names the new IO leaf, whose BAR page belongs to `f`, and every other
/// record and IO leaf of the table is unchanged.
proof fn install_io_4k_mapping_eof_pagetable_pci_mappings_wf(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires
        pre.inv(),
        install_io_4k_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        entry.is_io,
        pci_bar_function_of_page(pre.pci_bars.view(), entry.addr) == Some(f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None,
    ensures pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
{
    reveal(install_io_4k_mapping_eof_transition_framing);
    reveal(pagetable_pci_mappings_wf);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at;
}

/// The CPU caches close: the new leaf joins the table under a resolving L2 entry, the table's directory entries and held L2 entries
/// are unchanged, and recording its BAR mapping changes no walk.
proof fn install_io_4k_mapping_eof_cpu_caches(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires
        pre.inv(),
        install_io_4k_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        pagetable_lower_wf(mid.pt_mp, mid.pt_lower.view()),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
        cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
        structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(install_io_4k_mapping_eof_transition_framing);
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(mid.pt_mp, mid.pt_lower.view(), pagetable);
        tlb_wf_spec_preserved_for_4k_mapping_insert(mid.cpu_tlb, mid.cpu_arr, pre.pt_mp, pre.pt_lower.view(), mid.pt_mp, mid.pt_lower.view(), pagetable, va, mid.pcid_needflush);
        reveal(cpu_tlb_wf);
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, mid);
        reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match);
    };
}

/// EOF closure of `install_io_4k_mapping`: the kernel invariant holds after the IO leaf joins the table and its BAR mapping is
/// recorded.
pub(super) proof fn install_io_4k_mapping_eof(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires
        pre.inv(),
        install_io_4k_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        entry.is_io,
        pci_bar_function_of_page(pre.pci_bars.view(), entry.addr) == Some(f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        pagetable_lower_wf(mid.pt_mp, mid.pt_lower.view()),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        post.inv(),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(install_io_4k_mapping_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    install_io_4k_mapping_eof_page_tables(pre, mid, post, pagetable, va, f, entry);
    install_io_4k_mapping_eof_pagetable_pci_mappings_wf(pre, mid, post, pagetable, va, f, entry);
    install_io_4k_mapping_eof_cpu_caches(pre, mid, post, pagetable, va, f, entry);
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}

/// Installs the present IO 2M leaf `entry` at `va` in the write-held `pagetable` (from `pre` to `mid`, which keeps the big-lock
/// payload and resets its backup to the new window half) and then records the BAR mapping `(va, 2M)` under the function `f` (from
/// `mid` to `post`, which changes only the table's PCI function array); every other held entry, table, and kernel field, the page
/// array included, is unchanged.
#[verifier::opaque]
pub(super) open spec fn install_io_2m_mapping_eof_transition_framing(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let mid_c = whole_pagetable(mid.pt_mp, mid.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    &&& mid == (KernelK { pt_mp: mid.pt_mp, pt_lower: mid.pt_lower, ..pre })
    &&& mid.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& mid.pt_lower.view() == pre.pt_lower.view().insert(pagetable, mid.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(mid.pt_mp, mid.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& mid.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& mid.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& mid_c.higher == old_c.higher
    &&& mid_c.mapping_2m() == old_c.mapping_2m().insert(va, entry) && mid_c.mapping_4k() == old_c.mapping_4k() && mid_c.mapping_1g() == old_c.mapping_1g()
    &&& mid_c.page_closure() == old_c.page_closure()
    &&& mid_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger mid_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> mid_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger mid_c.spec_resolve_mapping_l2(l4i, l3i, l2i)] #![trigger old_c.spec_resolve_mapping_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> mid_c.spec_resolve_mapping_l2(l4i, l3i, l2i) == old_c.spec_resolve_mapping_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger mid_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> mid_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger mid_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
            ==> mid_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& mid_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
    &&& mid_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.addr == entry.addr
    &&& mid_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.perm.is_io == entry.is_io
    &&& post == (KernelK { pt_mp: post.pt_mp, ..mid })
    &&& post.pt_mp.unchanged_except(&mid.pt_mp, pagetable)
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == mid.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == mid.pt_mp.spec_index(pagetable).being_killed()
    &&& new_c.higher == (PageTableHigher { pci: new_c.higher.pci, ..mid_c.higher })
    &&& new_c.mapping_4k() == mid_c.mapping_4k() && new_c.mapping_2m() == mid_c.mapping_2m() && new_c.mapping_1g() == mid_c.mapping_1g() && new_c.page_closure() == mid_c.page_closure()
    &&& new_c.lower == mid_c.lower
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)] new_c.spec_held_l2(l4i, l3i, l2i) == mid_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)] new_c.spec_held_2m_l2(l4i, l3i, l2i) == mid_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == mid_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
        new_c.window_locked_by_thread(l4i, l3i, l2i, thread_id) == mid_c.window_locked_by_thread(l4i, l3i, l2i, thread_id)
    &&& new_c.kernel_l4_end() == mid_c.kernel_l4_end()
    &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_held_l4(l4i)] new_c.higher.spec_held_l4(l4i) == mid_c.higher.spec_held_l4(l4i)
    &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_resolve_mapping_l4(l4i)] new_c.higher.spec_resolve_mapping_l4(l4i) == mid_c.higher.spec_resolve_mapping_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_held_l3(l4i, l3i)] new_c.higher.spec_held_l3(l4i, l3i) == mid_c.higher.spec_held_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_l3(l4i, l3i)] new_c.higher.spec_resolve_mapping_l3(l4i, l3i) == mid_c.higher.spec_resolve_mapping_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_held_1g_l3(l4i, l3i)] new_c.higher.spec_held_1g_l3(l4i, l3i) == mid_c.higher.spec_held_1g_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)] new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i) == mid_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)
    &&& new_c.higher.pci.view() == mid_c.higher.pci.view().insert(f, mid_c.higher.pci.view()[f].insert((va, PageSize::SZ2m)))
    &&& new_c.higher.pci.view().dom() == old_c.higher.pci.view().dom()
    &&& forall|g: PciBdf, n: PciBarMapping| #![trigger new_c.higher.pci.view()[g].contains(n)] new_c.higher.pci.view().dom().contains(g)
        ==> new_c.higher.pci.view()[g].contains(n) == (old_c.higher.pci.view()[g].contains(n) || g == f && n == (va, PageSize::SZ2m))
}

/// The page-table relations close: the new leaf is an IO leaf no page lists, and the table's PCI function array, which owns `f`,
/// keeps its functions, so the table's process has not emptied its tables.
proof fn install_io_2m_mapping_eof_page_tables(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires
        pre.inv(),
        install_io_2m_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        entry.is_io,
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp),
{
    reveal(install_io_2m_mapping_eof_transition_framing);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid; reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_1g_valid_index_roundtrip, spec_index2va_2m_valid; reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp)) by { reveal(pci_function_ownership_wf); };
}

/// `pagetable_pci_mappings_wf`: the new record `(va, 2M)` of `f` names the new IO leaf, a 2M chunk of a BAR of `f`, and every other
/// record and IO leaf of the table is unchanged.
proof fn install_io_2m_mapping_eof_pagetable_pci_mappings_wf(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires
        pre.inv(),
        install_io_2m_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_v2l4index(va),
        entry.is_io,
        pci_bar_2m_chunk_of(pre.pci_bars.view(), entry.addr, f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
    ensures pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
{
    reveal(install_io_2m_mapping_eof_transition_framing);
    reveal(pagetable_pci_mappings_wf);
    pre.default_pagetable_wf_at(pagetable);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
}

/// The structure caches close: the table's held directory entries, their walks, and its window records are unchanged.
proof fn install_io_2m_mapping_eof_structure_cache(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires
        pre.inv(),
        install_io_2m_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
        pre.pt_mp.dom().contains(pagetable),
    ensures structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    install_io_2m_mapping_eof_resolve_l2(pre, mid, post, pagetable, va, f, entry);
    reveal(install_io_2m_mapping_eof_transition_framing);
    reveal(structure_cache_wf);
}

/// The L2 walks of `install_io_2m_mapping`: the new 2M leaf is huge, so no L2 entry resolves to an L1 page other than before.
proof fn install_io_2m_mapping_eof_resolve_l2(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires install_io_2m_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
    ensures
        forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_resolve_mapping_l2(l4i, l3i, l2i)]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l2(l4i, l3i, l2i),
{
    reveal(install_io_2m_mapping_eof_transition_framing);
}

/// EOF closure of `install_io_2m_mapping`: the kernel invariant holds after the IO leaf joins the table and its BAR mapping is
/// recorded.
pub(super) proof fn install_io_2m_mapping_eof(pre: KernelK, mid: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf, entry: MapEntry)
    requires
        pre.inv(),
        install_io_2m_mapping_eof_transition_framing(pre, mid, post, pagetable, va, f, entry),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_v2l4index(va),
        entry.is_io,
        pci_bar_2m_chunk_of(pre.pci_bars.view(), entry.addr, f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None,
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        pagetable_lower_wf(mid.pt_mp, mid.pt_lower.view()),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        post.inv(),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(install_io_2m_mapping_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    install_io_2m_mapping_eof_page_tables(pre, mid, post, pagetable, va, f, entry);
    install_io_2m_mapping_eof_pagetable_pci_mappings_wf(pre, mid, post, pagetable, va, f, entry);
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(mid.pt_mp, mid.pt_lower.view(), pagetable);
        pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m);
    };
    install_io_2m_mapping_eof_structure_cache(pre, mid, post, pagetable, va, f, entry);
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}
}
