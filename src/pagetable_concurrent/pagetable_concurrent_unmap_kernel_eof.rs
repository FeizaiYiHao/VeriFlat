use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `unmap_4k_page_kernel`: entry `target_l1i` of the L1 map `target_l1_p` is cleared and
    /// the 4K mapping of its address is removed; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn unmap_4k_page_kernel_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr) -> bool {
        let l2_p = pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr;
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, mapping_4k: post.lower.mapping_4k, ..pre.lower })
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(l2_p).addr() == l2_p && post.lower.l2_perms.spec_index(l2_p).is_init()
        &&& post.lower.l2_page(l2_p).addr() == l2_p
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(l2_p, target_l2i) == pre.lower.l2_entry(l2_p, target_l2i)
        &&& post.lower.l2_owner(l2_p, target_l2i) == pre.lower.l2_owner(l2_p, target_l2i)
        &&& pre.lower.l2_page(l2_p).entry_lock(target_l2i).l1() is Some && pre.lower.l1_perm(l2_p, target_l2i).addr() == target_l1_p
        &&& post.lower.l2_page(l2_p).entry_lock(target_l2i).l1() is Some
        &&& post.lower.l1_perm(l2_p, target_l2i).addr() == target_l1_p
        &&& post.lower.l1_perm(l2_p, target_l2i).is_init()
        &&& post.lower.l1_page(l2_p, target_l2i).wf()
        &&& forall|p: PageMapPtr, i: L2Index, j: L1Index| #![trigger post.lower.l1_page(p, i).spec_index(j)]
            p == l2_p && i == target_l2i && pei_valid(j) && j != target_l1i ==> post.lower.l1_page(p, i).spec_index(j) =~= pre.lower.l1_page(p, i).spec_index(j)
        &&& post.lower.l1_page(l2_p, target_l2i).spec_index(target_l1i).is_empty()
        &&& post.lower.mapping_4k == pre.lower.mapping_4k.remove(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)))
    }

    /// EOF closure of `unmap_4k_page_kernel`: every page-table invariant leaf, the unchanged page closure, and the
    /// cleared walk.
    pub(super) proof fn unmap_4k_page_kernel_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).present == false,
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
            post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::unmap_4k_page_kernel_eof_frame(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_hidden_l1_tables_in_locked_windows(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
    }

    /// EOF closure of `unmap_4k_page_kernel`: the leaves that read no L1 entry and no 4K mapping value.
    proof fn unmap_4k_page_kernel_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.higher.inv(),
            post.va_addr_valid(),
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.disjoint_l2(),
            post.wf_mapping_2m(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.wf_window_locks(),
            post.page_closure() =~= pre.page_closure(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        Self::unmap_4k_page_kernel_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `l3_links_l2_wf`.
    proof fn unmap_4k_page_kernel_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.l3_links_l2_wf(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::l3_links_l2_wf);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `wf_l2`.
    proof fn unmap_4k_page_kernel_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l2(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::wf_l2);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `disjoint_l2`.
    proof fn unmap_4k_page_kernel_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.disjoint_l2(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::disjoint_l2);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `wf_mapping_2m`.
    proof fn unmap_4k_page_kernel_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_2m);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `rwx_upper_level_entries`.
    proof fn unmap_4k_page_kernel_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::rwx_upper_level_entries);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `table_pages_wf`.
    proof fn unmap_4k_page_kernel_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.table_pages_wf(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::table_pages_wf);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `wf_window_locks`.
    proof fn unmap_4k_page_kernel_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_window_locks(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::wf_window_locks);
    }

    /// EOF closure of `unmap_4k_page_kernel`: the L1 leaves `wf_l1` and `user_only`.
    proof fn unmap_4k_page_kernel_eof_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l1(),
            post.user_only(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `wf_mapping_4k` and the cleared walk.
    proof fn unmap_4k_page_kernel_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_mapping_4k(),
            post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        post.resolve_l2_unchanged(&pre);
        assert(post.wf_mapping_4k()) by {
            reveal(WholePageTable::wf_mapping_4k);
            spec_index2va_injective();
            broadcast use WholePageTable::disjoint_l2_implies_resolve_l2_addr_unique_at, WholePageTable::wf_l2_implies_resolve_l2_target_in_l1_rev_map_at;
        };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `tables_reachable_wf`.
    proof fn unmap_4k_page_kernel_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `hidden_l1_tables_in_locked_windows`. The target entry and its lock are unchanged.
    proof fn unmap_4k_page_kernel_eof_hidden_l1_tables_in_locked_windows(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr)
        requires
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    { reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing); }

    /// EOF closure of `unmap_4k_page_kernel`: the target 4K leaf leaves the held chain; the rest is unchanged.
    pub(super) proof fn unmap_4k_page_kernel_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (target_l4i, target_l3i, target_l2i, target_l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            post.spec_held_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
        pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(target_l4i, target_l3i);
    }

    /// Operation-state summary of `clear_held_4k_leaf`: entry `target_l1i` of the L1 page that the held L2 entry `target_l2i` of the
    /// L2 page under `(target_l4i, target_l3i)` owns is cleared; that entry keeps its L1 page and lock, and every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn clear_held_4k_leaf_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index) -> bool {
        let l2_p = pre.spec_held_l3(target_l4i, target_l3i)->0.addr;
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, ..pre.lower })
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(l2_p).addr() == l2_p && post.lower.l2_perms.spec_index(l2_p).is_init()
        &&& post.lower.l2_page(l2_p).addr() == l2_p
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(l2_p, target_l2i) == pre.lower.l2_entry(l2_p, target_l2i)
        &&& post.lower.l2_owner(l2_p, target_l2i) == pre.lower.l2_owner(l2_p, target_l2i)
        &&& pre.lower.l2_page(l2_p).entry_lock(target_l2i).l1() is Some
        &&& post.lower.l2_page(l2_p).entry_lock(target_l2i).l1() is Some
        &&& post.lower.l1_perm(l2_p, target_l2i).addr() == pre.lower.l1_perm(l2_p, target_l2i).addr()
        &&& post.lower.l1_perm(l2_p, target_l2i).is_init()
        &&& post.lower.l1_page(l2_p, target_l2i).wf()
        &&& forall|p: PageMapPtr, i: L2Index, j: L1Index| #![trigger post.lower.l1_page(p, i).spec_index(j)]
            p == l2_p && i == target_l2i && pei_valid(j) && j != target_l1i ==> post.lower.l1_page(p, i).spec_index(j) =~= pre.lower.l1_page(p, i).spec_index(j)
        &&& post.lower.l1_page(l2_p, target_l2i).spec_index(target_l1i).is_empty()
    }

    /// EOF closure of `clear_held_4k_leaf`: every page-table invariant leaf and the unchanged page closure. No path to the leaf
    /// resolves, so every resolving 4K leaf reads another L1 page.
    pub(super) proof fn clear_held_4k_leaf_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            Self::clear_held_4k_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::clear_held_4k_leaf_eof_frame(pre, post, target_l4i, target_l3i, target_l2i, target_l1i);
        Self::clear_held_4k_leaf_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i);
        Self::clear_held_4k_leaf_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l1i);
    }

    /// EOF closure of `clear_held_4k_leaf`: the leaves that read no 4K walk, and the unchanged page closure.
    proof fn clear_held_4k_leaf_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index)
        requires
            pre.wf(),
            Self::clear_held_4k_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i),
        ensures
            post.higher.inv(),
            post.va_addr_valid(),
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.wf_mapping_2m(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.wf_window_locks(),
            post.page_closure() =~= pre.page_closure(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        reveal(WholePageTable::clear_held_4k_leaf_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
        assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
    }

    /// EOF closure of `clear_held_4k_leaf`: `tables_reachable_wf`; the target L2 entry keeps its L1 page and address.
    proof fn clear_held_4k_leaf_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index)
        requires
            pre.wf(),
            Self::clear_held_4k_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::clear_held_4k_leaf_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    }

    /// EOF closure of `clear_held_4k_leaf`: `wf_mapping_4k`; a resolving 4K leaf sits under a resolving L3 path, whose L2 page is not
    /// the target's.
    proof fn clear_held_4k_leaf_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            Self::clear_held_4k_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(WholePageTable::clear_held_4k_leaf_eof_transition_framing);
        post.resolve_l2_unchanged(&pre);
        assert(post.wf_mapping_4k()) by {
            reveal(WholePageTable::wf_mapping_4k);
            broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
        };
    }

    /// EOF closure of `clear_held_4k_leaf`: the target 4K leaf leaves the held chain; the rest is unchanged.
    pub(super) proof fn clear_held_4k_leaf_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            Self::clear_held_4k_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (target_l4i, target_l3i, target_l2i, target_l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            post.spec_held_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
            forall|w: WindowVa| #![trigger post.window_view(w)]
                pre.kernel_l4_end() <= spec_v2l4index(w.va) && pei_valid(spec_v2l4index(w.va)) && pei_valid(spec_v2l3index(w.va)) && pre.window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                    ==> post.window_view(w) == pre.window_view(w),
    {
        reveal(WholePageTable::clear_held_4k_leaf_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
    }
}
} // verus!
