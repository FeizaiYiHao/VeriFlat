use vstd::prelude::*;
use crate::*;

verus! {
/// Clears the present bit of the 2M leaf `va` in the window half of `pagetable`, whose L2 page is `l2_ptr`: only that window's
/// L2 entry changes, keeping its address and staying the held 2M leaf; the stale-CPU map, every other mapping and held entry,
/// and every other table and kernel field are unchanged.
#[verifier::opaque]
pub(super) open spec fn clear_2m_mapping_present_in_window_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr) -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let target = (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
    &&& post == (KernelK { pt_lower: post.pt_lower, ..pre })
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& new_c.mapping_2m() == old_c.mapping_2m().insert(va, MapEntry { present: false, ..old_c.mapping_2m().spec_index(va) })
    &&& new_c.mapping_4k() == old_c.mapping_4k()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (l2_ptr, target.2) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& new_c.lower.l2_entry(l2_ptr, target.2) == (PageEntry { perm: PageEntryPerm { present: false, ..old_c.lower.l2_entry(l2_ptr, target.2).perm }, ..old_c.lower.l2_entry(l2_ptr, target.2) })
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != target ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
    &&& new_c.spec_held_2m_l2(target.0, target.1, target.2) == Some(new_c.lower.l2_entry(l2_ptr, target.2))
}

/// The cleared leaf is still held with its address and access bits, so the TLBs stay inside the table.
proof fn clear_2m_mapping_present_in_window_eof_tlb(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        clear_2m_mapping_present_in_window_eof_transition_framing(pre, post, pagetable, va, l2_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_v2l2index(va))),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index((l2_ptr, spec_v2l2index(va))) == Set::range(0usize, NUM_CPUS),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
    ensures cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(clear_2m_mapping_present_in_window_eof_transition_framing);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let (l4i, l3i, l2i) = (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
    broadcast use spec_va_2m_valid_index_roundtrip;
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
    old_c.wf_mapping_2m_at(l4i, l3i, l2i); old_c.spec_resolve_mapping_2m_l2_some_implies_spec_held_2m_l2_eq(l4i, l3i, l2i);
    reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip;
}

/// Clearing the present bit of a 2M leaf, which owns no L1 page, keeps every held L2 entry; the window lists every CPU stale.
proof fn clear_2m_mapping_present_in_window_eof_structure_cache(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        clear_2m_mapping_present_in_window_eof_transition_framing(pre, post, pagetable, va, l2_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_v2l2index(va))),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index((l2_ptr, spec_v2l2index(va))) == Set::range(0usize, NUM_CPUS),
    ensures structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(clear_2m_mapping_present_in_window_eof_transition_framing);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    broadcast use spec_va_2m_valid_index_roundtrip;
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
    old_c.wf_mapping_2m_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
    reveal(structure_cache_wf);
}

pub(super) proof fn clear_2m_mapping_present_in_window_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        clear_2m_mapping_present_in_window_eof_transition_framing(pre, post, pagetable, va, l2_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr == l2_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_v2l2index(va))),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index((l2_ptr, spec_v2l2index(va))) == Set::range(0usize, NUM_CPUS),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures post.inv(),
{
    reveal(clear_2m_mapping_present_in_window_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(post.memory_management_inv()) by {
        assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
        pre.default_pagetable_wf_at(pagetable);
        assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by {
            broadcast use spec_va_4k_valid_index_roundtrip, spec_va_4k_index_roundtrip_at; reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf);
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
    clear_2m_mapping_present_in_window_eof_tlb(pre, post, pagetable, va, l2_ptr);
    clear_2m_mapping_present_in_window_eof_structure_cache(pre, post, pagetable, va, l2_ptr);
}
}
