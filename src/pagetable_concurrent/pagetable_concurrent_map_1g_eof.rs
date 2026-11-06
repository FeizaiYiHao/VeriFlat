use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `map_1g_page`: entry `target_l3i` of the L3 page `target_l3_p` now holds the present 1G leaf of
    /// `target_entry`, which joins `mapping_1g`; the window half and every other field are unchanged.
    #[verifier::opaque]
    pub open spec fn map_1g_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: MapEntry) -> bool {
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
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i)
            =~= (PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } })
        &&& post.higher.mapping_1g.view() == pre.higher.mapping_1g.view().insert(spec_index2va((target_l4i, target_l3i, 0, 0)), target_entry)
    }

    /// EOF closure of `map_1g_page`: every page-table invariant leaf and the unchanged page closure.
    pub(super) proof fn map_1g_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_1g_valid(target_entry.addr),
            page_table_key_1g_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, 0, 0))),
            target_entry.present,
            Self::map_1g_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_entry),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
    {
        Self::map_1g_page_eof_higher_inv(pre, post, target_l4i, target_l3i, target_l3_p, target_entry);
        Self::map_1g_page_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l3_p, target_entry);
        Self::map_1g_page_eof_mappings(pre, post, target_l4i, target_l3i, target_l3_p, target_entry);
    }

    /// EOF closure of `map_1g_page`: the big-lock invariant; the new leaf is huge, so no L3 link changes.
    proof fn map_1g_page_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_1g_valid(target_entry.addr),
            page_table_key_1g_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, 0, 0))),
            target_entry.present,
            Self::map_1g_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_entry),
        ensures
            post.higher.inv(),
    {
        Self::map_1g_page_eof_wf_mapping_1g(pre, post, target_l4i, target_l3i, target_l3_p, target_entry);
        reveal(WholePageTable::map_1g_page_eof_transition_framing);
        assert(post.higher.va_addr_valid()) by { spec_index2va_injective(); };
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

    /// EOF closure of `map_1g_page`: `wf_mapping_1g`; the new leaf resolves under the present root entry and every other walk is
    /// unchanged.
    proof fn map_1g_page_eof_wf_mapping_1g(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_1g_valid(target_entry.addr),
            page_table_key_1g_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, 0, 0))),
            target_entry.present,
            Self::map_1g_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_entry),
        ensures
            post.higher.wf_mapping_1g(),
    {
        Self::map_1g_page_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p, target_entry);
        reveal(WholePageTable::map_1g_page_eof_transition_framing);
        reveal(PageTableHigher::wf_mapping_1g);
        spec_index2va_injective();
    }

    /// EOF closure of `map_1g_page`: the leaves of the window half that read no walk, and the unchanged page closure.
    proof fn map_1g_page_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            Self::map_1g_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_entry),
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
        reveal(WholePageTable::map_1g_page_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `map_1g_page`: the leaves that read the L3 walk; every L3 link resolves and is held as before.
    proof fn map_1g_page_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            Self::map_1g_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_entry),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
            post.tables_reachable_wf(),
            post.wf_window_locks(),
    {
        Self::map_1g_page_eof_resolve(pre, post, target_l4i, target_l3i, target_l3_p, target_entry);
        Self::map_1g_page_eof_held_chain(pre, post, target_l4i, target_l3i, target_l3_p, target_entry);
        reveal(WholePageTable::map_1g_page_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); };
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
        assert(post.wf_window_locks()) by {
            reveal(WholePageTable::wf_window_locks); reveal(WholePageTable::tables_reachable_wf);
            broadcast use spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip;
        };
    }

    /// EOF closure of `map_1g_page`: the new leaf resolves; every other walk and every window owner are unchanged.
    pub(super) proof fn map_1g_page_eof_resolve(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            Self::map_1g_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_entry),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_resolve_mapping_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_resolve_mapping_l4(l4i) == pre.spec_resolve_mapping_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_resolve_mapping_l3(l4i, l3i) == pre.spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_resolve_mapping_1g_l3(l4i, l3i) == pre.spec_resolve_mapping_1g_l3(l4i, l3i),
            post.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) == Some(PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId| #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        reveal(WholePageTable::map_1g_page_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }

    /// EOF closure of `map_1g_page`: the new leaf is held; the rest of the held chain is unchanged.
    pub(super) proof fn map_1g_page_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            Self::map_1g_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_entry),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_l3(l4i, l3i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_held_l3(l4i, l3i) == pre.spec_held_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_held_1g_l3(l4i, l3i) == pre.spec_held_1g_l3(l4i, l3i),
            post.spec_held_1g_l3(target_l4i, target_l3i) == Some(PageEntry { addr: target_entry.addr, perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } }),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
    {
        reveal(WholePageTable::map_1g_page_eof_transition_framing);
        reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
    }
}
} // verus!
