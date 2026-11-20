use vstd::prelude::*;
use crate::*;

verus! {
/// Clears the held, unresolvable IO 4K leaf `va` of `pagetable`; every other held entry of the table and every other kernel field,
/// the page array included, is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_held_io_4k_mapping_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr) -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& new_c.higher == old_c.higher
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g() && new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
            ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& new_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
}

/// The page-table relations close: the page array is unchanged and no page lists the removed IO leaf.
proof fn remove_held_io_4k_mapping_eof_page_tables(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        remove_held_io_4k_mapping_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None,
        pre.pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.perm.is_io,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(remove_held_io_4k_mapping_eof_transition_framing);
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
}

/// `pagetable_pci_mappings_wf`: the table, whose PCI functions were released, records no mapping and has no present IO leaf, and
/// every IO leaf left in the tables was held before.
proof fn remove_held_io_4k_mapping_eof_pagetable_pci_mappings_wf(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        remove_held_io_4k_mapping_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty(),
    ensures pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
{
    reveal(remove_held_io_4k_mapping_eof_transition_framing);
    reveal(pagetable_pci_mappings_wf);
    pre.default_pagetable_wf_at(pagetable);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
}

/// EOF closure of `remove_held_io_4k_mapping`: the kernel invariant holds after the IO leaf leaves the table.
pub(super) proof fn remove_held_io_4k_mapping_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        remove_held_io_4k_mapping_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None,
        pre.pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.perm.is_io,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(remove_held_io_4k_mapping_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    remove_held_io_4k_mapping_eof_page_tables(pre, post, pagetable, va);
    remove_held_io_4k_mapping_eof_pagetable_pci_mappings_wf(pre, post, pagetable, va);
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
    };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    assert(pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp)) by { reveal(pci_function_ownership_wf); };
}

/// Clears the held, unresolvable IO 2M leaf `va` of `pagetable`; every other held entry of the table and every other kernel field,
/// the page array included, is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_held_io_2m_mapping_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr) -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let leaf = (old_c.spec_held_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr, spec_v2l2index(va));
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& new_c.higher == old_c.higher
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g() && new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != leaf ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& new_c.lower.l2_entry(leaf.0, leaf.1).is_empty()
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
            ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& new_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
}

/// The page-table relations close: the page array is unchanged and no page lists the removed IO leaf.
proof fn remove_held_io_2m_mapping_eof_page_tables(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        remove_held_io_2m_mapping_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None,
        pre.pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.perm.is_io,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(remove_held_io_2m_mapping_eof_transition_framing);
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
}

/// `pagetable_pci_mappings_wf`: the table, whose PCI functions were released, records no mapping and has no present IO leaf, and
/// every IO leaf left in the tables was held before.
proof fn remove_held_io_2m_mapping_eof_pagetable_pci_mappings_wf(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        remove_held_io_2m_mapping_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty(),
    ensures pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
{
    reveal(remove_held_io_2m_mapping_eof_transition_framing);
    reveal(pagetable_pci_mappings_wf);
    pre.default_pagetable_wf_at(pagetable);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
}

/// EOF closure of `remove_held_io_2m_mapping`: the kernel invariant holds after the IO leaf leaves the table.
pub(super) proof fn remove_held_io_2m_mapping_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        remove_held_io_2m_mapping_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l4(spec_v2l4index(va)) is None,
        pre.pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))->0.perm.is_io,
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom() == Set::<PciBdf>::empty(),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(remove_held_io_2m_mapping_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    remove_held_io_2m_mapping_eof_page_tables(pre, post, pagetable, va);
    remove_held_io_2m_mapping_eof_pagetable_pci_mappings_wf(pre, post, pagetable, va);
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); };
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp); };
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
    };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    assert(pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp)) by { reveal(pci_function_ownership_wf); };
}

/// Removes the hidden IO 4K leaf `va` of the write-held `pagetable` under its window and drops its BAR mapping `(va, 4K)` from the
/// function `f`; the table keeps its L2 entries and every other held leaf, its payload backup follows the new window half, and every
/// other kernel field, the page array included, is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_io_4k_mapping_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf) -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& new_c.higher == (PageTableHigher { pci: new_c.higher.pci, ..old_c.higher })
    &&& new_c.kernel_l4_end() == old_c.kernel_l4_end()
    &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_held_l4(l4i)] new_c.higher.spec_held_l4(l4i) == old_c.higher.spec_held_l4(l4i)
    &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_resolve_mapping_l4(l4i)] new_c.higher.spec_resolve_mapping_l4(l4i) == old_c.higher.spec_resolve_mapping_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_held_l3(l4i, l3i)] new_c.higher.spec_held_l3(l4i, l3i) == old_c.higher.spec_held_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_l3(l4i, l3i)] new_c.higher.spec_resolve_mapping_l3(l4i, l3i) == old_c.higher.spec_resolve_mapping_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_held_1g_l3(l4i, l3i)] new_c.higher.spec_held_1g_l3(l4i, l3i) == old_c.higher.spec_held_1g_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)] new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i) == old_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)
    &&& new_c.higher.pci.view() == old_c.higher.pci.view().insert(f, old_c.higher.pci.view()[f].remove((va, PageSize::SZ4k)))
    &&& new_c.higher.pci.view().dom() == old_c.higher.pci.view().dom()
    &&& forall|g: PciBdf, n: PciBarMapping| #![trigger new_c.higher.pci.view()[g].contains(n)] new_c.higher.pci.view().dom().contains(g)
        ==> new_c.higher.pci.view()[g].contains(n) == (old_c.higher.pci.view()[g].contains(n) && !(g == f && n == (va, PageSize::SZ4k)))
    &&& new_c.mapping_4k() == old_c.mapping_4k().remove(va) && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
            ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& new_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) is None
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
}

/// The page-table relations close: the page array is unchanged, no page lists the removed IO leaf, and the table's PCI function
/// array keeps its functions.
proof fn remove_io_4k_mapping_eof_page_tables(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf)
    requires
        pre.inv(),
        remove_io_4k_mapping_eof_transition_framing(pre, post, pagetable, va, f),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().spec_index(va).is_io,
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp),
{
    reveal(remove_io_4k_mapping_eof_transition_framing);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at;
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).wf_mapping_4k_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
        reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
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

/// `pagetable_pci_mappings_wf`: the dropped record `(va, 4K)` of `f` named the removed IO leaf, every other record of the table
/// names a leaf at another key, and every IO leaf left was recorded before at a key other than `va`.
proof fn remove_io_4k_mapping_eof_pagetable_pci_mappings_wf(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf)
    requires
        pre.inv(),
        remove_io_4k_mapping_eof_transition_framing(pre, post, pagetable, va, f),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view()[f].contains((va, PageSize::SZ4k)),
    ensures pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
{
    reveal(remove_io_4k_mapping_eof_transition_framing);
    reveal(pagetable_pci_mappings_wf);
    pre.default_pagetable_wf_at(pagetable);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at;
}

/// EOF closure of `remove_io_4k_mapping`: the kernel invariant holds after the IO leaf and its BAR mapping record leave the table.
pub(super) proof fn remove_io_4k_mapping_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, f: PciBdf)
    requires
        pre.inv(),
        remove_io_4k_mapping_eof_transition_framing(pre, post, pagetable, va, f),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().spec_index(va).is_io,
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view()[f].contains((va, PageSize::SZ4k)),
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
    reveal(remove_io_4k_mapping_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    remove_io_4k_mapping_eof_page_tables(pre, post, pagetable, va, f);
    remove_io_4k_mapping_eof_pagetable_pci_mappings_wf(pre, post, pagetable, va, f);
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}

/// Removes the hidden IO 2M leaf `va` of the write-held `pagetable` under its window and drops its BAR mapping `(va, 2M)` from the
/// function `f`; only the leaf's L2 entry in the L2 page `l2_ptr` changes in the window half, the payload backup follows it, and every
/// other kernel field, the page array included, is unchanged.
#[verifier::opaque]
pub(super) open spec fn remove_io_2m_mapping_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, f: PciBdf)
    -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& new_c.higher == (PageTableHigher { pci: new_c.higher.pci, ..old_c.higher })
    &&& new_c.kernel_l4_end() == old_c.kernel_l4_end()
    &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_held_l4(l4i)] new_c.higher.spec_held_l4(l4i) == old_c.higher.spec_held_l4(l4i)
    &&& forall|l4i: L4Index| #![trigger new_c.higher.spec_resolve_mapping_l4(l4i)] new_c.higher.spec_resolve_mapping_l4(l4i) == old_c.higher.spec_resolve_mapping_l4(l4i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_held_l3(l4i, l3i)] new_c.higher.spec_held_l3(l4i, l3i) == old_c.higher.spec_held_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_l3(l4i, l3i)] new_c.higher.spec_resolve_mapping_l3(l4i, l3i) == old_c.higher.spec_resolve_mapping_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_held_1g_l3(l4i, l3i)] new_c.higher.spec_held_1g_l3(l4i, l3i) == old_c.higher.spec_held_1g_l3(l4i, l3i)
    &&& forall|l4i: L4Index, l3i: L3Index| #![trigger new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)] new_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i) == old_c.higher.spec_resolve_mapping_1g_l3(l4i, l3i)
    &&& new_c.higher.pci.view() == old_c.higher.pci.view().insert(f, old_c.higher.pci.view()[f].remove((va, PageSize::SZ2m)))
    &&& new_c.higher.pci.view().dom() == old_c.higher.pci.view().dom()
    &&& forall|g: PciBdf, n: PciBarMapping| #![trigger new_c.higher.pci.view()[g].contains(n)] new_c.higher.pci.view().dom().contains(g)
        ==> new_c.higher.pci.view()[g].contains(n) == (old_c.higher.pci.view()[g].contains(n) && !(g == f && n == (va, PageSize::SZ2m)))
    &&& new_c.mapping_2m() == old_c.mapping_2m().remove(va)
    &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_1g() == old_c.mapping_1g() && new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_owner(p, i) == old_c.lower.l2_owner(p, i)
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (l2_ptr, spec_v2l2index(va)) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
            ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& new_c.spec_held_2m_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is None
}

/// The page-table relations close: the page array is unchanged, no page lists the removed IO leaf, and the table's PCI function
/// array keeps its functions.
proof fn remove_io_2m_mapping_eof_page_tables(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, f: PciBdf)
    requires
        pre.inv(),
        remove_io_2m_mapping_eof_transition_framing(pre, post, pagetable, va, l2_ptr, f),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(va).is_io,
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp),
{
    reveal(remove_io_2m_mapping_eof_transition_framing);
    pre.default_pagetable_wf_at(pagetable);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).wf_mapping_2m_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
        broadcast use spec_va_1g_valid_index_roundtrip, spec_index2va_2m_valid; reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_lower_wf);
    };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
    assert(pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp)) by { reveal(pci_function_ownership_wf); };
}

/// `pagetable_pci_mappings_wf`: the dropped record `(va, 2M)` of `f` named the removed IO leaf, every other record of the table
/// names a leaf at another key, and every IO leaf left was recorded before at a key other than `va`.
proof fn remove_io_2m_mapping_eof_pagetable_pci_mappings_wf(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, f: PciBdf)
    requires
        pre.inv(),
        remove_io_2m_mapping_eof_transition_framing(pre, post, pagetable, va, l2_ptr, f),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view()[f].contains((va, PageSize::SZ2m)),
    ensures pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
{
    reveal(remove_io_2m_mapping_eof_transition_framing);
    reveal(pagetable_pci_mappings_wf);
    pre.default_pagetable_wf_at(pagetable);
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
}

/// EOF closure of `remove_io_2m_mapping`: the kernel invariant holds after the IO leaf and its BAR mapping record leave the table.
pub(super) proof fn remove_io_2m_mapping_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, f: PciBdf)
    requires
        pre.inv(),
        remove_io_2m_mapping_eof_transition_framing(pre, post, pagetable, va, l2_ptr, f),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().spec_index(va).is_io,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_v2l2index(va))),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view().dom().contains(f),
        pre.pt_mp.spec_index(pagetable).view().higher.pci.view()[f].contains((va, PageSize::SZ2m)),
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
    reveal(remove_io_2m_mapping_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    remove_io_2m_mapping_eof_page_tables(pre, post, pagetable, va, l2_ptr, f);
    remove_io_2m_mapping_eof_pagetable_pci_mappings_wf(pre, post, pagetable, va, l2_ptr, f);
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    assert(structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        broadcast use spec_va_2m_valid_index_roundtrip;
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).wf_mapping_2m_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        reveal(structure_cache_wf); reveal(cpu_dirty_map_pagetable_pcid_match);
    };
    assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, post.ep_mp)) by { kernel_endpoint_nonlock_fields_unchanged_for_equal(pre.ep_mp, post.ep_mp); };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}
}
