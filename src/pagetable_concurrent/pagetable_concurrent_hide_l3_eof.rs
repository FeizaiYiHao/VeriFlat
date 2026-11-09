use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `hide_l3_entry`: entry `target_l3i` of the L3 page `target_l3_p` is a placeholder for the same L2 page and the 512 windows under it leave the window lock map; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn hide_l3_entry_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr) -> bool {
        &&& post.higher == (PageTableHigher { l3_tables: post.higher.l3_tables, ..pre.higher })
        &&& post.lower == (PageTableLower { pagetable_window_locks: post.lower.pagetable_window_locks, ..pre.lower })
        &&& post.higher.l3_tables.view().dom() == pre.higher.l3_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.higher.l3_tables.view().spec_index(p)]
            pre.higher.l3_tables.view().dom().contains(p) && p != target_l3_p ==> post.higher.l3_tables.view().spec_index(p) == pre.higher.l3_tables.view().spec_index(p)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).is_init()
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().wf()
        &&& forall|i: usize| #![trigger post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
            pei_valid(i) && i != target_l3i ==> post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i)
            =~= (PageEntry { addr: pre.higher.l3_entry(target_l3_p, target_l3i).addr, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } })
        &&& post.lower.pagetable_window_locks == pre.lower.pagetable_window_locks.remove_keys(pre.lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i))
    }

    /// EOF closure of `hide_l3_entry`: every page-table invariant leaf and the unchanged page closure.
    pub(super) proof fn hide_l3_entry_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i)] pei_valid(i) ==> pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index, j: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j)]
                pei_valid(i) && pei_valid(j) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j) is None,
            Self::hide_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::hide_l3_entry_eof_higher_inv(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::hide_l3_entry_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::hide_l3_entry_eof_mappings(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::hide_l3_entry_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l3_p);
    }

    /// EOF closure of `hide_l3_entry`: the big-lock invariant; the placeholder links the same L2 page and is no 1G leaf.
    proof fn hide_l3_entry_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i)] pei_valid(i) ==> pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index, j: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j)]
                pei_valid(i) && pei_valid(j) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j) is None,
            Self::hide_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.higher.inv(),
    {
        reveal(WholePageTable::hide_l3_entry_eof_transition_framing);
        assert(post.higher.wf_l4()) by { reveal(PageTableHigher::wf_l4); };
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `hide_l3_entry`: the leaves of the window half that read no walk, the unchanged page closure, and the hidden L1
    /// pages, which stay in their unchanged L2 pages.
    proof fn hide_l3_entry_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i)] pei_valid(i) ==> pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index, j: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j)]
                pei_valid(i) && pei_valid(j) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j) is None,
            Self::hide_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
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
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        reveal(WholePageTable::hide_l3_entry_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `hide_l3_entry`: the 4K and 2M mappings, none of which resolved under the entry, and `tables_reachable_wf`, which reads
    /// the held chain.
    proof fn hide_l3_entry_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i)] pei_valid(i) ==> pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index, j: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j)]
                pei_valid(i) && pei_valid(j) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j) is None,
            Self::hide_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
            post.tables_reachable_wf(),
    {
        Self::hide_l3_entry_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p);
        Self::hide_l3_entry_eof_held_chain(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(WholePageTable::hide_l3_entry_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); };
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    }

    /// EOF closure of `hide_l3_entry`: `wf_window_locks`; the windows under the entry leave the map with its walk, and the L2 page under it,
    /// now unresolvable, was unlocked.
    proof fn hide_l3_entry_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i)] pei_valid(i) ==> pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index, j: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j)]
                pei_valid(i) && pei_valid(j) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j) is None,
            Self::hide_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            post.wf_window_locks(),
    {
        Self::hide_l3_entry_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p);
        reveal(WholePageTable::hide_l3_entry_eof_transition_framing);
        reveal(WholePageTable::tables_reachable_wf); reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4); reveal(WholePageTable::l3_links_l2_wf);
        spec_index2va_injective();
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq, spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip;
        reveal(WholePageTable::wf_window_locks);
    }

    /// EOF closure of `hide_l3_entry`: no walk passes the placeholder; every other walk and every window owner are unchanged.
    pub(super) proof fn hide_l3_entry_eof_resolve(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i)] pei_valid(i) ==> pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index, j: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j)]
                pei_valid(i) && pei_valid(j) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j) is None,
            Self::hide_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_resolve_mapping_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_resolve_mapping_l4(l4i) == pre.spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_resolve_mapping_l3(l4i, l3i) == pre.spec_resolve_mapping_l3(l4i, l3i),
            post.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i, l3i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_resolve_mapping_1g_l3(l4i, l3i) == pre.spec_resolve_mapping_1g_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l2i: L2Index| #![trigger post.spec_resolve_mapping_l2(target_l4i, target_l3i, l2i)] pei_valid(l2i) ==> post.spec_resolve_mapping_l2(target_l4i, target_l3i, l2i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        reveal(WholePageTable::hide_l3_entry_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }

    /// EOF closure of `hide_l3_entry`: the placeholder holds the same L2 page, so the held chain is unchanged below it.
    pub(super) proof fn hide_l3_entry_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i)] pei_valid(i) ==> pre.lower.l2_owner(pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index, j: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j)]
                pei_valid(i) && pei_valid(j) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, i, j) is None,
            Self::hide_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_held_l3(l4i, l3i) == pre.spec_held_l3(l4i, l3i),
            post.spec_held_l3(target_l4i, target_l3i) == Some(PageEntry { addr: pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } }),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_1g_l3(l4i, l3i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_held_1g_l3(l4i, l3i) == pre.spec_held_1g_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
    {
        reveal(WholePageTable::hide_l3_entry_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }
}
} // verus!
