use vstd::prelude::*;
use crate::*;

verus! {
/// Clears the present bit of the 4K leaf `va` in the window half of `pagetable`, keeping its stale-CPU map, its L2 entries
/// and every other held leaf; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn clear_4k_mapping_present_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr) -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& post.pt_mp.spec_index(pagetable).locking_thread() == pre.pt_mp.spec_index(pagetable).locking_thread()
    &&& post.pt_mp.spec_index(pagetable).being_killed() == pre.pt_mp.spec_index(pagetable).being_killed()
    &&& forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) ==> post.pt_mp.spec_index(p).view().higher == pre.pt_mp.spec_index(p).view().higher
    &&& post.pt_mp.spec_index(pagetable).view().lower_backup == if pre.pt_mp.spec_index(pagetable).wlocked() { Ghost(post.pt_lower.view().spec_index(pagetable)) } else { pre.pt_mp.spec_index(pagetable).view().lower_backup }
    &&& new_c.mapping_4k() == old_c.mapping_4k().insert(va, MapEntry { present: false, ..old_c.mapping_4k().spec_index(va) })
    &&& new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != spec_va2index(va)
            ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& new_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)) == Some(PageEntry {
            perm: PageEntryPerm { present: false, ..old_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0.perm },
            ..old_c.spec_held_4k_l1(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))->0
        })
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
}

/// `pagetable_pci_mappings_wf`: the hidden leaf at `va` stays held with its target and IO bit, so its record still holds, and no
/// longer being present it needs none; every other leaf and record is unchanged.
proof fn clear_4k_mapping_present_eof_pagetable_pci_mappings_wf(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pagetable_pci_mappings_wf(pre.pci_bars.view(), pre.pt_mp, pre.pt_lower.view()),
        pagetable_lower_wf(pre.pt_mp, pre.pt_lower.view()),
        clear_4k_mapping_present_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
    ensures pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view()),
{
    reveal(clear_4k_mapping_present_eof_transition_framing);
    broadcast use spec_va_4k_valid_index_roundtrip;
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
    whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).wf_mapping_4k_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
    whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
    reveal(pagetable_pci_mappings_wf);
}

/// `pci_function_ownership_wf`: the root table, the processes and every PCI function array are unchanged.
proof fn clear_4k_mapping_present_eof_pci_function_ownership_wf(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pci_function_ownership_wf(pre.irt.view(), pre.prc_mp, pre.pt_mp),
        clear_4k_mapping_present_eof_transition_framing(pre, post, pagetable, va),
    ensures pci_function_ownership_wf(post.irt.view(), post.prc_mp, post.pt_mp),
{
    reveal(clear_4k_mapping_present_eof_transition_framing);
    reveal(pci_function_ownership_wf);
}

pub(super) proof fn clear_4k_mapping_present_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        clear_4k_mapping_present_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        pre.pt_mp.spec_index(pagetable).view().higher.kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index((whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va)))
            == Set::range(0usize, NUM_CPUS),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures post.inv(),
{
    reveal(clear_4k_mapping_present_eof_transition_framing);
    clear_4k_mapping_present_eof_pagetable_pci_mappings_wf(pre, post, pagetable, va);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(post.memory_management_inv()) by {
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        pre.default_pagetable_wf_at(pagetable);
        assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at;
            pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).wf_mapping_4k_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_4k_l1_some_implies_spec_held_4k_l1_eq(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
            reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
        };
        assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { broadcast use spec_va_2m_valid_index_roundtrip; reveal(mapped_2m_page_pagetable_wf); };
        assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
        assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); };
        assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); };
        assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_pagetable_pcid_match); };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
    clear_4k_mapping_present_eof_pci_function_ownership_wf(pre, post, pagetable, va);
}
}
