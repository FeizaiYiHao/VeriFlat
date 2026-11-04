use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `hide_l4_entry`: root entry `target_l4i` is now a placeholder for the same L3 page, and every 4K,
    /// 2M and 1G mapping and every window under it leaves its map; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn hide_l4_entry_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index) -> bool {
        &&& post.higher == (PageTableHigher { l4_table: post.higher.l4_table, mapping_1g: post.higher.mapping_1g, ..pre.higher })
        &&& post.lower == (PageTableLower { mapping_4k: post.lower.mapping_4k, mapping_2m: post.lower.mapping_2m, pagetable_window_locks: post.lower.pagetable_window_locks, ..pre.lower })
        &&& post.higher.l4_table.view().dom() == pre.higher.l4_table.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.higher.l4_table.view().spec_index(p)]
            pre.higher.l4_table.view().dom().contains(p) && p != pre.higher.cr3 ==> post.higher.l4_table.view().spec_index(p) == pre.higher.l4_table.view().spec_index(p)
        &&& post.higher.l4_table.view().spec_index(pre.higher.cr3).addr() == pre.higher.cr3
        &&& post.higher.l4_table.view().spec_index(pre.higher.cr3).is_init()
        &&& post.higher.l4_table.view().spec_index(pre.higher.cr3).value().wf()
        &&& forall|i: usize| #![trigger post.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(i)]
            pei_valid(i) && i != target_l4i ==> post.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(i) =~= pre.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(i)
        &&& post.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(target_l4i) =~= (PageEntry {
            addr: pre.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(target_l4i).addr, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } })
        &&& post.higher.mapping_1g.view() == pre.higher.mapping_1g.view().remove_keys(pre.higher.mapping_1g.view().dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i))
        &&& post.lower.mapping_4k == pre.lower.mapping_4k.remove_keys(pre.lower.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i))
        &&& post.lower.mapping_2m == pre.lower.mapping_2m.remove_keys(pre.lower.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == target_l4i))
        &&& post.lower.pagetable_window_locks == pre.lower.pagetable_window_locks.remove_keys(pre.lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i))
    }

    /// EOF closure of `hide_l4_entry`: every page-table invariant leaf.
    pub(super) proof fn hide_l4_entry_eof(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            forall|p: PageMapPtr, i: L2Index| #![trigger pre.lower.l2_owner(p, i)] pre.lower.l2_perms.dom().contains(p) && pre.higher.l2_rev_map.view().spec_index(p).0 == target_l4i && pei_valid(i) ==> pre.lower.l2_owner(p, i) is None,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::hide_l4_entry_eof_higher_inv(pre, post, target_l4i);
        Self::hide_l4_entry_eof_table_leaves(pre, post, target_l4i);
        Self::hide_l4_entry_eof_wf_mapping_4k(pre, post, target_l4i);
        Self::hide_l4_entry_eof_wf_mapping_2m(pre, post, target_l4i);
        Self::hide_l4_entry_eof_wf_window_locks(pre, post, target_l4i);
        assert(post.page_closure() =~= pre.page_closure() && (pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows())) by { reveal(WholePageTable::hide_l4_entry_eof_transition_framing); };
    }

    /// EOF closure of `hide_l4_entry`: the big-lock invariant; the placeholder still links the same L3 page.
    proof fn hide_l4_entry_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            post.higher.inv(),
    {
        Self::hide_l4_entry_eof_wf_mapping_1g(pre, post, target_l4i);
        reveal(WholePageTable::hide_l4_entry_eof_transition_framing);
        assert(post.higher.va_addr_valid());
        assert(post.higher.wf_l4()) by { reveal(PageTableHigher::wf_l4); };
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `hide_l4_entry`: `wf_mapping_1g`; every 1G leaf under the root entry leaves the map with its walk.
    proof fn hide_l4_entry_eof_wf_mapping_1g(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            post.higher.wf_mapping_1g(),
    {
        Self::hide_l4_entry_eof_resolve(pre, post, target_l4i);
        reveal(WholePageTable::hide_l4_entry_eof_transition_framing);
        reveal(PageTableHigher::wf_mapping_1g);
        spec_index2va_injective();
        broadcast use spec_va_1g_valid_index_roundtrip, iova_1g_valid_index_roundtrip;
    }

    /// EOF closure of `hide_l4_entry`: the leaves that read no walk below the root, and `tables_reachable_wf`, which reads the held chain.
    proof fn hide_l4_entry_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            post.va_addr_valid(),
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::hide_l4_entry_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    }

    /// EOF closure of `hide_l4_entry`: `wf_mapping_4k`; every 4K leaf under the root entry leaves the map with its walk.
    proof fn hide_l4_entry_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(WholePageTable::hide_l4_entry_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_4k);
        spec_index2va_injective();
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip, iova_4k_valid_index_roundtrip, iova_2m_valid_index_roundtrip, iova_1g_valid_index_roundtrip;
    }

    /// EOF closure of `hide_l4_entry`: `wf_mapping_2m`; every 2M leaf under the root entry leaves the map with its walk.
    proof fn hide_l4_entry_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::hide_l4_entry_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_2m);
        spec_index2va_injective();
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip, iova_4k_valid_index_roundtrip, iova_2m_valid_index_roundtrip, iova_1g_valid_index_roundtrip;
    }

    /// EOF closure of `hide_l4_entry`: `wf_window_locks`; every window under the root entry leaves the map with its walk, and
    /// the L2 pages under it, now unresolvable, were all unlocked.
    proof fn hide_l4_entry_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            forall|p: PageMapPtr, i: L2Index| #![trigger pre.lower.l2_owner(p, i)] pre.lower.l2_perms.dom().contains(p) && pre.higher.l2_rev_map.view().spec_index(p).0 == target_l4i && pei_valid(i) ==> pre.lower.l2_owner(p, i) is None,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            post.wf_window_locks(),
    {
        Self::hide_l4_entry_eof_resolve(pre, post, target_l4i);
        reveal(WholePageTable::hide_l4_entry_eof_transition_framing);
        reveal(WholePageTable::wf_window_locks);
        reveal(WholePageTable::tables_reachable_wf);
        spec_index2va_injective();
        broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip, iova_4k_valid_index_roundtrip, iova_2m_valid_index_roundtrip, iova_1g_valid_index_roundtrip;
    }

    /// EOF closure of `hide_l4_entry`: the root entry no longer resolves and every walk under another root entry is unchanged.
    pub(super) proof fn hide_l4_entry_eof_resolve(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            post.spec_resolve_mapping_l4(target_l4i) is None,
            forall|l4i: L4Index| #![trigger post.spec_resolve_mapping_l4(l4i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && l4i != target_l4i ==> post.spec_resolve_mapping_l4(l4i) == pre.spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && l4i != target_l4i ==> post.spec_resolve_mapping_l3(l4i, l3i) == pre.spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && l4i != target_l4i ==> post.spec_resolve_mapping_1g_l3(l4i, l3i) == pre.spec_resolve_mapping_1g_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && l4i != target_l4i ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && l4i != target_l4i ==> post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && l4i != target_l4i ==> post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
    {
        reveal(WholePageTable::hide_l4_entry_eof_transition_framing);
    }

    /// EOF closure of `hide_l4_entry`: the placeholder holds the same L3 page, so the held chain is unchanged below it.
    pub(super) proof fn hide_l4_entry_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            Self::hide_l4_entry_eof_transition_framing(pre, post, target_l4i),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && l4i != target_l4i ==> post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
            post.spec_held_l4(target_l4i) == Some(PageEntry { addr: pre.spec_held_l4(target_l4i)->0.addr,
                perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_held_l3(l4i, l3i) == pre.spec_held_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
    {
        reveal(WholePageTable::hide_l4_entry_eof_transition_framing);
    }
}
} // verus!
