use vstd::prelude::*;
verus! {
use crate::*;

impl WholePageTable {
    /// Operation-state summary of `hide_1g_leaf`: the 1G leaf in entry `target_l3i` of the L3 page `target_l3_p` has its user present bit clear and its `mapping_1g` record is no longer present; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn hide_1g_leaf_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr) -> bool {
        &&& post.lower == pre.lower
        &&& post.higher == (PageTableHigher { l3_tables: post.higher.l3_tables, mapping_1g: post.higher.mapping_1g, ..pre.higher })
        &&& post.higher.l3_tables.view().dom() == pre.higher.l3_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.higher.l3_tables.view().spec_index(p)]
            pre.higher.l3_tables.view().dom().contains(p) && p != target_l3_p ==> post.higher.l3_tables.view().spec_index(p) == pre.higher.l3_tables.view().spec_index(p)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).is_init()
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().wf()
        &&& forall|i: usize| #![trigger post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
            pei_valid(i) && i != target_l3i ==> post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i) =~= (PageEntry { perm: PageEntryPerm { present: false, ..pre.higher.l3_entry(target_l3_p, target_l3i).perm },
            ..pre.higher.l3_entry(target_l3_p, target_l3i) })
        &&& post.higher.mapping_1g.view() == pre.higher.mapping_1g.view().insert(spec_index2va((target_l4i, target_l3i, 0, 0)),
            MapEntry { present: false, ..pre.higher.mapping_1g.view().spec_index(spec_index2va((target_l4i, target_l3i, 0, 0))) })
    }

    /// EOF closure of `hide_1g_leaf`: every page-table invariant leaf and the unchanged page closure.
    pub(super) proof fn hide_1g_leaf_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is Some,
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
    {
        Self::hide_1g_leaf_eof_higher_inv(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::hide_1g_leaf_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::hide_1g_leaf_eof_mappings(pre, post, target_l4i, target_l3i, target_l3_p);
    }

    /// EOF closure of `hide_1g_leaf`: the user-entry half of `wf_l4`; the root level is unchanged.
    proof fn hide_1g_leaf_eof_wf_l4_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|i: L4Index|
                #![trigger post.higher.l4_entry(i).perm.present]
                post.higher.kernel_l4_end <= i && pei_valid(i) && (post.higher.l4_entry(i).perm.present || post.higher.l4_entry(i).perm.kernel_present) ==> {
                    &&& !post.higher.l4_entry(i).perm.ps
                    &&& post.higher.l3_tables.view().dom().contains(post.higher.l4_entry(i).addr)
                },
    {
        reveal(WholePageTable::hide_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `hide_1g_leaf`: the root half of `wf_l4`; the L4 table is unchanged.
    proof fn hide_1g_leaf_eof_wf_l4_root(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.higher.l4_table.view().dom() =~= Set::<PageMapPtr>::empty().insert(post.higher.cr3),
            post.higher.cr3 == post.higher.l4_table.view().spec_index(post.higher.cr3).addr(),
            post.higher.l4_table.view().spec_index(post.higher.cr3).is_init(),
            post.higher.l4_table.view().spec_index(post.higher.cr3).value().wf(),
    {
        reveal(WholePageTable::hide_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `hide_1g_leaf`: `wf_l4`.
    proof fn hide_1g_leaf_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.higher.wf_l4(),
    {
        Self::hide_1g_leaf_eof_wf_l4_root(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::hide_1g_leaf_eof_wf_l4_entries(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `hide_1g_leaf`: the big-lock invariant.
    proof fn hide_1g_leaf_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is Some,
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.higher.inv(),
    {
        Self::hide_1g_leaf_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(WholePageTable::hide_1g_leaf_eof_transition_framing);
        assert(post.higher.va_addr_valid()) by { pre.higher.wf_mapping_1g_at(target_l4i, target_l3i); };
        Self::hide_1g_leaf_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l3_p);
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); spec_index2va_injective(); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `hide_1g_leaf`: the leaves of the window half that read no walk, and the unchanged page closure.
    proof fn hide_1g_leaf_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is Some,
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.va_addr_valid(),
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.page_closure() =~= pre.page_closure(),
    {
        reveal(WholePageTable::hide_1g_leaf_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `hide_1g_leaf`: the leaves that read the L3 walk; every L3 link resolves and is held as before.
    proof fn hide_1g_leaf_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is Some,
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
            post.tables_reachable_wf(),
            post.wf_window_locks(),
    {
        Self::hide_1g_leaf_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::hide_1g_leaf_eof_nonempty_chain(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(WholePageTable::hide_1g_leaf_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); };
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
        assert(post.wf_window_locks()) by {
            reveal(WholePageTable::wf_window_locks); reveal(WholePageTable::tables_reachable_wf);
            broadcast use spec_va_2m_valid_index_roundtrip;
        };
    }

    /// EOF closure of `hide_1g_leaf`: the walks through the changed entry and every unchanged walk.
    pub(super) proof fn hide_1g_leaf_eof_resolve(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is Some,
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_resolve_mapping_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_resolve_mapping_l4(l4i) == pre.spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_l3(l4i, l3i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> post.spec_resolve_mapping_l3(l4i, l3i) == pre.spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_resolve_mapping_1g_l3(l4i, l3i) == pre.spec_resolve_mapping_1g_l3(l4i, l3i),
            post.spec_resolve_mapping_1g_l3(target_l4i, target_l3i)
                == Some(PageEntry { perm: PageEntryPerm { present: false, ..pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i)->0.perm }, ..pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i)->0 }),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        reveal(WholePageTable::hide_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }

    /// EOF closure of `hide_1g_leaf`: the non-empty root and L3 entries through the changed entry and every unchanged one.
    pub(super) proof fn hide_1g_leaf_eof_nonempty_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is Some,
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_nonempty_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_nonempty_l4(l4i) == pre.spec_nonempty_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_nonempty_l3(l4i, l3i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_nonempty_l3(l4i, l3i) == pre.spec_nonempty_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_nonempty_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_nonempty_1g_l3(l4i, l3i) == pre.spec_nonempty_1g_l3(l4i, l3i),
            post.spec_nonempty_1g_l3(target_l4i, target_l3i)
                == Some(PageEntry { perm: PageEntryPerm { present: false, ..pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i)->0.perm }, ..pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i)->0 }),
    {
        reveal(WholePageTable::hide_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }

    /// EOF closure of `hide_1g_leaf`: every non-empty entry below an L3 entry, whose non-empty L3 walk is unchanged, over the unchanged lower half.
    pub(super) proof fn hide_1g_leaf_eof_nonempty_lower_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            Self::hide_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_nonempty_l3(l4i, l3i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_nonempty_l3(l4i, l3i) == pre.spec_nonempty_l3(l4i, l3i),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_nonempty_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_nonempty_l2(l4i, l3i, l2i) == pre.spec_nonempty_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_nonempty_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_nonempty_2m_l2(l4i, l3i, l2i) == pre.spec_nonempty_2m_l2(l4i, l3i, l2i),
    {
        reveal(WholePageTable::hide_1g_leaf_eof_transition_framing);
    }

    /// Operation-state summary of `clear_nonempty_1g_leaf`: entry `target_l3i` of the L3 page `target_l3_p`, which held a 1G leaf, is cleared and the leaf leaves `mapping_1g`; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn clear_nonempty_1g_leaf_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr) -> bool {
        &&& post.lower == pre.lower
        &&& post.higher == (PageTableHigher { l3_tables: post.higher.l3_tables, mapping_1g: post.higher.mapping_1g, ..pre.higher })
        &&& post.higher.l3_tables.view().dom() == pre.higher.l3_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.higher.l3_tables.view().spec_index(p)]
            pre.higher.l3_tables.view().dom().contains(p) && p != target_l3_p ==> post.higher.l3_tables.view().spec_index(p) == pre.higher.l3_tables.view().spec_index(p)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).is_init()
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().wf()
        &&& forall|i: usize| #![trigger post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
            pei_valid(i) && i != target_l3i ==> post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).is_empty()
        &&& post.higher.mapping_1g.view() == pre.higher.mapping_1g.view().remove(spec_index2va((target_l4i, target_l3i, 0, 0)))
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: every page-table invariant leaf and the unchanged page closure.
    pub(super) proof fn clear_nonempty_1g_leaf_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_nonempty_l4(target_l4i) is Some,
            pre.spec_nonempty_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_nonempty_1g_l3(target_l4i, target_l3i) is Some,
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
    {
        Self::clear_nonempty_1g_leaf_eof_higher_inv(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::clear_nonempty_1g_leaf_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::clear_nonempty_1g_leaf_eof_mappings(pre, post, target_l4i, target_l3i, target_l3_p);
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the user-entry half of `wf_l4`.
    proof fn clear_nonempty_1g_leaf_eof_wf_l4_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|i: L4Index|
                #![trigger post.higher.l4_entry(i).perm.present]
                post.higher.kernel_l4_end <= i && pei_valid(i) && (post.higher.l4_entry(i).perm.present || post.higher.l4_entry(i).perm.kernel_present) ==> {
                    &&& !post.higher.l4_entry(i).perm.ps
                    &&& post.higher.l3_tables.view().dom().contains(post.higher.l4_entry(i).addr)
                },
    {
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the root half of `wf_l4`; the L4 table is unchanged.
    proof fn clear_nonempty_1g_leaf_eof_wf_l4_root(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.higher.l4_table.view().dom() =~= Set::<PageMapPtr>::empty().insert(post.higher.cr3),
            post.higher.cr3 == post.higher.l4_table.view().spec_index(post.higher.cr3).addr(),
            post.higher.l4_table.view().spec_index(post.higher.cr3).is_init(),
            post.higher.l4_table.view().spec_index(post.higher.cr3).value().wf(),
    {
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: `wf_l4`.
    proof fn clear_nonempty_1g_leaf_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.higher.wf_l4(),
    {
        Self::clear_nonempty_1g_leaf_eof_wf_l4_root(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::clear_nonempty_1g_leaf_eof_wf_l4_entries(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the big-lock invariant.
    proof fn clear_nonempty_1g_leaf_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_nonempty_l4(target_l4i) is Some,
            pre.spec_nonempty_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_nonempty_1g_l3(target_l4i, target_l3i) is Some,
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.higher.inv(),
    {
        Self::clear_nonempty_1g_leaf_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        assert(post.higher.va_addr_valid()) by { spec_index2va_injective(); };
        Self::clear_nonempty_1g_leaf_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l3_p);
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); spec_index2va_injective(); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the leaves of the window half that read no walk, and the unchanged page closure.
    proof fn clear_nonempty_1g_leaf_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_nonempty_l4(target_l4i) is Some,
            pre.spec_nonempty_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_nonempty_1g_l3(target_l4i, target_l3i) is Some,
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.va_addr_valid(),
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.page_closure() =~= pre.page_closure(),
    {
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the leaves that read the L3 walk; every L3 link resolves and is held as before.
    proof fn clear_nonempty_1g_leaf_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_nonempty_l4(target_l4i) is Some,
            pre.spec_nonempty_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_nonempty_1g_l3(target_l4i, target_l3i) is Some,
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
            post.tables_reachable_wf(),
            post.wf_window_locks(),
    {
        Self::clear_nonempty_1g_leaf_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::clear_nonempty_1g_leaf_eof_nonempty_chain(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); };
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
        assert(post.wf_window_locks()) by {
            reveal(WholePageTable::wf_window_locks); reveal(WholePageTable::tables_reachable_wf);
            broadcast use spec_va_2m_valid_index_roundtrip;
        };
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the walks through the changed entry and every unchanged walk.
    pub(super) proof fn clear_nonempty_1g_leaf_eof_resolve(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_nonempty_l4(target_l4i) is Some,
            pre.spec_nonempty_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_nonempty_1g_l3(target_l4i, target_l3i) is Some,
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_resolve_mapping_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_resolve_mapping_l4(l4i) == pre.spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_l3(l4i, l3i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> post.spec_resolve_mapping_l3(l4i, l3i) == pre.spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_resolve_mapping_1g_l3(l4i, l3i) == pre.spec_resolve_mapping_1g_l3(l4i, l3i),
            post.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the non-empty L2 entries and 4K leaves are unchanged.
    pub(super) proof fn clear_nonempty_1g_leaf_eof_nonempty_l2_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_nonempty_l4(target_l4i) is Some,
            pre.spec_nonempty_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_nonempty_1g_l3(target_l4i, target_l3i) is Some,
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_nonempty_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_nonempty_l2(l4i, l3i, l2i) == pre.spec_nonempty_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_nonempty_4k_l1(l4i, l3i, l2i, l1i),
    {
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the non-empty 2M leaves are unchanged.
    pub(super) proof fn clear_nonempty_1g_leaf_eof_nonempty_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_nonempty_l4(target_l4i) is Some,
            pre.spec_nonempty_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_nonempty_1g_l3(target_l4i, target_l3i) is Some,
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_nonempty_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_nonempty_2m_l2(l4i, l3i, l2i) == pre.spec_nonempty_2m_l2(l4i, l3i, l2i),
    {
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }

    /// EOF closure of `clear_nonempty_1g_leaf`: the non-empty chain through the changed entry and every unchanged non-empty entry.
    pub(super) proof fn clear_nonempty_1g_leaf_eof_nonempty_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_nonempty_l4(target_l4i) is Some,
            pre.spec_nonempty_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_nonempty_1g_l3(target_l4i, target_l3i) is Some,
            Self::clear_nonempty_1g_leaf_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_nonempty_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_nonempty_l4(l4i) == pre.spec_nonempty_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_nonempty_l3(l4i, l3i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_nonempty_l3(l4i, l3i) == pre.spec_nonempty_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_nonempty_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_nonempty_1g_l3(l4i, l3i) == pre.spec_nonempty_1g_l3(l4i, l3i),
            post.spec_nonempty_1g_l3(target_l4i, target_l3i) is None,
    {
        Self::clear_nonempty_1g_leaf_eof_nonempty_l2_4k(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::clear_nonempty_1g_leaf_eof_nonempty_2m(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(WholePageTable::clear_nonempty_1g_leaf_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }
}
} // verus!
