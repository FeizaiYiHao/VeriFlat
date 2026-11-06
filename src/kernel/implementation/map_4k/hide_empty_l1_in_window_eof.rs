use vstd::prelude::*;
use crate::*;

verus! {
/// Hides the L1 page that the window of `va`, whose L2 page is `l2_ptr`, links in the window half of `pagetable`: only that
/// window's L2 entry changes, still held and naming the same page but no longer resolving; the stale-CPU map, every mapping,
/// every held leaf, and every other table and kernel field are unchanged.
#[verifier::opaque]
pub(super) open spec fn hide_empty_l1_in_window_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr) -> bool {
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let target = (spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2);
    &&& post == (KernelK { pt_lower: post.pt_lower, ..pre })
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable, post.pt_lower.view().spec_index(pagetable))
    &&& forall|p: RwLockPageTableRoot| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), p)]
        pre.pt_mp.dom().contains(p) && p != pagetable ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), p) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), p)
    &&& new_c.mapping_4k() == old_c.mapping_4k()
    &&& new_c.mapping_2m() == old_c.mapping_2m()
    &&& new_c.mapping_1g() == old_c.mapping_1g()
    &&& new_c.page_closure() == old_c.page_closure()
    &&& new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
    &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks
    &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_entry(p, i)] (p, i) != (l2_ptr, target.2) ==> new_c.lower.l2_entry(p, i) == old_c.lower.l2_entry(p, i)
    &&& new_c.lower.l2_entry(l2_ptr, target.2).addr == old_c.lower.l2_entry(l2_ptr, target.2).addr
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != target ==> new_c.spec_held_l2(l4i, l3i, l2i) == old_c.spec_held_l2(l4i, l3i, l2i)
    &&& new_c.spec_held_l2(target.0, target.1, target.2) == Some(new_c.lower.l2_entry(l2_ptr, target.2))
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_resolve_mapping_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != target
            ==> new_c.spec_resolve_mapping_l2(l4i, l3i, l2i) == old_c.spec_resolve_mapping_l2(l4i, l3i, l2i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> new_c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == old_c.spec_held_4k_l1(l4i, l3i, l2i, l1i)
    &&& forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger new_c.spec_held_2m_l2(l4i, l3i, l2i)]
        old_c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> new_c.spec_held_2m_l2(l4i, l3i, l2i) == old_c.spec_held_2m_l2(l4i, l3i, l2i)
}

/// The paging-structure caches stay inside the table: the hidden entry is still held with its address and lists every CPU stale.
proof fn hide_empty_l1_in_window_eof_structure_cache(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        hide_empty_l1_in_window_eof_transition_framing(pre, post, pagetable, va, l2_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_va2index(va).2)),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index((l2_ptr, spec_va2index(va).2)) == Set::range(0usize, NUM_CPUS),
    ensures structure_cache_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(hide_empty_l1_in_window_eof_transition_framing);
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
    spec_va_4k_index_roundtrip_at(va, spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3);
    old_c.spec_resolve_mapping_l2_some_implies_spec_held_l2_eq(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2);
    reveal(structure_cache_wf);
}

/// The window resolves no 4K leaf before the hide, so no entry of the hidden L1 page has the kernel_present bit set.
pub(super) proof fn hide_empty_l1_in_window_eof_hidden_l1_empty(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        hide_empty_l1_in_window_eof_transition_framing(pre, post, pagetable, va, l2_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) is Some,
        forall|l1i: L1Index| #![trigger whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, l1i)))]
            pei_valid(l1i) ==> !whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, l1i))),
    ensures
        forall|l1i: L1Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l1_page(l2_ptr, spec_va2index(va).2).spec_index(l1i)]
            pei_valid(l1i) ==> !whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l1_page(l2_ptr, spec_va2index(va).2).spec_index(l1i).perm.kernel_present,
{
    reveal(hide_empty_l1_in_window_eof_transition_framing);
    let c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let (l4i, l3i, l2i) = (spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2);
    spec_va_4k_index_roundtrip_at(va, l4i, l3i, l2i, spec_va2index(va).3);
    pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
    c.spec_resolve_mapping_l2_some_implies_spec_held_l2_eq(l4i, l3i, l2i); c.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(l4i, l3i);
    let d = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    assert forall|l1i: L1Index| #![trigger pei_valid(l1i)] pei_valid(l1i) implies !d.lower.l1_page(l2_ptr, l2i).spec_index(l1i).perm.kernel_present by {
        reveal(WholePageTable::wf_mapping_4k); c.wf_mapping_4k_at(l4i, l3i, l2i, l1i);
        assert(c.spec_held_4k_l1(l4i, l3i, l2i, l1i) == c.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) && d.spec_held_4k_l1(l4i, l3i, l2i, l1i) == c.spec_held_4k_l1(l4i, l3i, l2i, l1i));
        assert(d.spec_held_l3(l4i, l3i) == c.spec_held_l3(l4i, l3i) && d.spec_held_l2(l4i, l3i, l2i) is Some);
    };
}

pub(super) proof fn hide_empty_l1_in_window_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr)
    requires
        pre.inv(),
        hide_empty_l1_in_window_eof_transition_framing(pre, post, pagetable, va, l2_ptr),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((l2_ptr, spec_va2index(va).2)),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.spec_index((l2_ptr, spec_va2index(va).2)) == Set::range(0usize, NUM_CPUS),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
    ensures
        post.inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
{
    reveal(hide_empty_l1_in_window_eof_transition_framing);
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
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable); pagetable_lower_wf_at(post.pt_mp, post.pt_lower.view(), pagetable);
        reveal(cpu_tlb_wf); reveal(WholePageTable::wf_mapping_4k); reveal(WholePageTable::wf_mapping_2m); broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip;
    };
    hide_empty_l1_in_window_eof_structure_cache(pre, post, pagetable, va, l2_ptr);
    assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &post)) by {
        reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_iommu_table_nonlock_fields_unchanged);
        kernel_cpu_nonlock_fields_unchanged_for_equal(pre.cpu_arr, post.cpu_arr);
        kernel_process_nonlock_fields_unchanged_for_equal(pre.prc_mp, post.prc_mp);
    };
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
}
/// The hide changes only the L2 entry and the stale-CPU record of the window of `va`, so every other window this thread holds
/// keeps its view.
pub(super) proof fn hide_empty_l1_in_window_eof_held_windows(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr, l2_ptr: PageMapPtr, lctx: LocalContext)
    requires
        pre.inv(),
        typed_lock_maps_aligned(&pre, &lctx),
        pre.pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).kernel_l4_end() <= spec_va2index(va).0,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) is Some,
        whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1)->0.addr == l2_ptr,
        post.pt_mp.spec_index(pagetable).view() == pre.pt_mp.spec_index(pagetable).view(),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.window_stale_cpus
            == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.window_stale_cpus.insert((l2_ptr, spec_va2index(va).2), Set::range(0usize, NUM_CPUS)),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l2_entry(p, i)]
            (p, i) != (l2_ptr, spec_va2index(va).2) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l2_entry(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_entry(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l2_owner(p, i) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l2_page(p).entry_lock(i).l1()]
            whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && (p, i) != (l2_ptr, spec_va2index(va).2)
                ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).lower.l2_page(p).entry_lock(i).l1() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).lower.l2_page(p).entry_lock(i).l1(),
    ensures
        forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && w != window_of(va)
            ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable).window_view(w) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable).window_view(w),
{
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    let vi = spec_va2index(va);
    spec_va_4k_index_roundtrip_at(va, vi.0, vi.1, vi.2, vi.3);
    spec_va_4k_index_roundtrip_at(window_of(va).va, vi.0, vi.1, vi.2, 0usize);
    pagetable_perms_wf_map(pre.pt_mp); pagetable_perms_wf_at(pre.pt_mp, pagetable); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
    assert forall|w: WindowVa| #![trigger lctx.pagetable_window_lock_map().dom().contains((pagetable, w))] lctx.pagetable_window_lock_map().dom().contains((pagetable, w)) && w != window_of(va)
        implies new_c.window_view(w) == old_c.window_view(w) by {
        let l4w = spec_v2l4index(w.va);
        let l3w = spec_v2l3index(w.va);
        let l2w = spec_v2l2index(w.va);
        pagetable_window_typed_lock_map_aligned_at(pre.pt_mp, pre.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, w);
        spec_va_2m_valid_index_roundtrip(w.va);
        spec_index2va_injective();
        old_c.higher.disjoint_l4_l3_implies_resolve_l3_addr_unique_at(l4w, l3w, vi.0, vi.1);
        old_c.higher.wf_l4_at(l4w);
        old_c.l3_links_l2_wf_at(old_c.spec_resolve_mapping_l4(l4w)->0.addr, l3w);
        assert((old_c.window_l2_page(l4w, l3w), l2w) != (l2_ptr, vi.2));
    };
}
}
