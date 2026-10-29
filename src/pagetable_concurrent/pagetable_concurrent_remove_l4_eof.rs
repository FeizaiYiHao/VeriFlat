use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    /// Operation-state summary of `remove_l4_entry`: the root map's entry `target_l4i` is cleared and the L3 page
    /// `target_l3_p` leaves the L3 pages and their reverse index; the window half and every other field are unchanged.
    #[verifier::opaque]
    pub open spec fn remove_l4_entry_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr) -> bool {
        &&& post.lower == pre.lower
        &&& post.higher == (PageTableHigher { l4_table: post.higher.l4_table, l3_rev_map: post.higher.l3_rev_map, l3_tables: post.higher.l3_tables, ..pre.higher })
        &&& post.higher.l3_rev_map.view() == pre.higher.l3_rev_map.view().remove(target_l3_p)
        &&& post.higher.l3_tables.view() == pre.higher.l3_tables.view().remove(target_l3_p)
        &&& post.higher.l4_table.view() =~= pre.higher.l4_table.view().insert(pre.cr3(), post.higher.l4_table.view().spec_index(pre.cr3()))
        &&& post.higher.l4_table.view().dom() =~= pre.higher.l4_table.view().dom()
        &&& post.higher.l4_table.view().spec_index(pre.cr3()).addr() == pre.cr3()
        &&& post.higher.l4_table.view().spec_index(pre.cr3()).is_init()
        &&& post.higher.l4_table.view().spec_index(pre.cr3()).value().wf()
        &&& forall|i: usize|
            #![trigger pre.higher.l4_table.view().spec_index(pre.cr3()).value().spec_index(i)]
            #![trigger post.higher.l4_table.view().spec_index(pre.cr3()).value().spec_index(i)]
            pei_valid(i) && i != target_l4i ==> post.higher.l4_table.view().spec_index(pre.cr3()).value().spec_index(i) =~= pre.higher.l4_table.view().spec_index(pre.cr3()).value().spec_index(i)
        &&& post.higher.l4_table.view().spec_index(pre.cr3()).value().spec_index(target_l4i).is_empty()
    }

    /// EOF closure of `remove_l4_entry`: every page-table invariant leaf and the shrunk page closure.
    pub(super) proof fn remove_l4_entry_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![trigger pre.spec_resolve_mapping_l3(target_l4i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![trigger pre.spec_resolve_mapping_1g_l3(target_l4i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            pre.higher.l3_tables.view().dom().contains(target_l3_p),
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l3_p),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger pre.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        Self::remove_l4_entry_eof_higher(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_frame(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_walks(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_wf_window_locks(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_window_locked_by_thread(pre, post, target_l4i, target_l3_p);
    }

    /// EOF closure of `remove_l4_entry`: the big-lock half `higher.inv()`.
    proof fn remove_l4_entry_eof_higher(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![trigger pre.spec_resolve_mapping_1g_l3(target_l4i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.higher.inv(),
    {
        reveal(PageTableC::remove_l4_entry_eof_transition_framing);
        assert(post.higher.wf_l4()) by { reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `remove_l4_entry`: the window-half leaves that read no walk, and the shrunk page closure.
    proof fn remove_l4_entry_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.higher.l3_tables.view().dom().contains(target_l3_p),
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.va_addr_valid(),
            post.wf_l3(),
            post.l2_tokens_paired(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l3_p),
    {
        reveal(PageTableC::remove_l4_entry_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
        assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
        assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
        assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
        assert(post.user_only()) by { reveal(PageTableC::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
        assert(post.page_closure() =~= pre.page_closure().remove(target_l3_p)) by { reveal(PageTableC::table_pages_wf); reveal(PageTableHigher::table_pages_wf); };
    }

    /// EOF closure of `remove_l4_entry`: the leaves that read walks through the root, `wf_mapping_4k`, `wf_mapping_2m`,
    /// and `tables_reachable_wf`.
    proof fn remove_l4_entry_eof_walks(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![trigger pre.spec_resolve_mapping_l3(target_l4i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
            post.tables_reachable_wf(),
    {
        reveal(PageTableC::remove_l4_entry_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); reveal(PageTableHigher::disjoint_l4); };
        assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); reveal(PageTableHigher::disjoint_l4); };
        assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); reveal(PageTableHigher::disjoint_l4); };
    }

    /// EOF closure of `remove_l4_entry`: `wf_window_locks`, kept apart from the walk leaves because its index roundtrip
    /// broadcasts stall `wf_mapping_2m` in a shared query.
    proof fn remove_l4_entry_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![trigger pre.spec_resolve_mapping_l3(target_l4i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_window_locks(),
    {
        reveal(PageTableC::remove_l4_entry_eof_transition_framing);
        assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); reveal(PageTableHigher::disjoint_l4); broadcast use spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip; };
    }

    /// EOF closure of `remove_l4_entry`: window lock owners. No window hangs under the cleared root entry and the
    /// window half is unchanged.
    proof fn remove_l4_entry_eof_window_locked_by_thread(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![trigger pre.spec_resolve_mapping_l3(target_l4i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger pre.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        reveal(PageTableC::remove_l4_entry_eof_transition_framing);
        reveal(PageTableHigher::disjoint_l4);
    }
}
} // verus!
