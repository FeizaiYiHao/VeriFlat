use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `clear_held_2m_leaf`: the held 2M leaf entry `target_l2i` of the L2 page under `(target_l4i, target_l3i)`
    /// is published cleared; it owned no L1 page and keeps its lock, and every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn clear_held_2m_leaf_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index) -> bool {
        let l2_p = pre.spec_held_l3(target_l4i, target_l3i)->0.addr;
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, ..pre.lower })
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(l2_p).addr() == l2_p && post.lower.l2_perms.spec_index(l2_p).is_init()
        &&& post.lower.l2_page(l2_p).addr() == l2_p
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(l2_p, target_l2i).is_empty()
        &&& post.lower.l2_owner(l2_p, target_l2i) == pre.lower.l2_owner(l2_p, target_l2i)
        &&& pre.lower.l2_page(l2_p).entry_lock(target_l2i).l1() is None
        &&& post.lower.l2_page(l2_p).entry_lock(target_l2i).l1() is None
    }

    /// EOF closure of `clear_held_2m_leaf`: every page-table invariant leaf and the unchanged page closure. No path to the leaf
    /// resolves, so every resolving leaf reads another L2 page.
    pub(super) proof fn clear_held_2m_leaf_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            Self::clear_held_2m_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::clear_held_2m_leaf_eof_frame(pre, post, target_l4i, target_l3i, target_l2i);
        Self::clear_held_2m_leaf_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i);
        Self::clear_held_2m_leaf_eof_mappings(pre, post, target_l4i, target_l3i, target_l2i);
    }

    /// EOF closure of `clear_held_2m_leaf`: the leaves that read no walk, and the unchanged page closure.
    proof fn clear_held_2m_leaf_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            Self::clear_held_2m_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i),
        ensures
            post.higher.inv(),
            post.va_addr_valid(),
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.wf_window_locks(),
            post.page_closure() =~= pre.page_closure(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        reveal(WholePageTable::clear_held_2m_leaf_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
        assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
    }

    /// EOF closure of `clear_held_2m_leaf`: `tables_reachable_wf`; no L2 entry changed its L1 page.
    proof fn clear_held_2m_leaf_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index)
        requires
            pre.wf(),
            Self::clear_held_2m_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::clear_held_2m_leaf_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    }

    /// EOF closure of `clear_held_2m_leaf`: the 4K and 2M abstract-mapping leaves; a resolving leaf sits under a resolving L3 path, whose
    /// L2 page is not the target's.
    proof fn clear_held_2m_leaf_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            Self::clear_held_2m_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::clear_held_2m_leaf_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq; };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq; };
    }

    /// EOF closure of `clear_held_2m_leaf`: the target 2M leaf leaves the held chain; the rest is unchanged.
    pub(super) proof fn clear_held_2m_leaf_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            Self::clear_held_2m_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            post.spec_held_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|w: WindowVa| #![trigger post.window_view(w)]
                pre.kernel_l4_end() <= spec_v2l4index(w.va) && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va)) && pre.window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                    ==> post.window_view(w) == pre.window_view(w),
    {
        reveal(WholePageTable::clear_held_2m_leaf_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
    }
}
} // verus!
