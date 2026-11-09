use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `remove_l2_entry`: entry `target_l2i` of the L2 page `target_l2_p` is cleared and the
    /// L1 page `target_l1_p` leaves the L1 pages and their reverse index; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn remove_l2_entry_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, l1_rev_map: post.lower.l1_rev_map, ..pre.lower })
        &&& post.lower.l1_rev_map == pre.lower.l1_rev_map.remove(target_l1_p)
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != target_l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(target_l2_p).addr() == target_l2_p && post.lower.l2_perms.spec_index(target_l2_p).is_init()
        &&& post.lower.l2_page(target_l2_p).addr() == target_l2_p
        &&& post.lower.l2_page(target_l2_p).wf()
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == target_l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(target_l2_p, target_l2i).is_empty()
        &&& post.lower.l2_owner(target_l2_p, target_l2i) == pre.lower.l2_owner(target_l2_p, target_l2i)
        &&& post.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is None
    }

    /// EOF closure of `remove_l2_entry`: every page-table invariant leaf and the shrunk page closure.
    pub(super) proof fn remove_l2_entry_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            forall|i: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i) is None,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l1_p),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger pre.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::remove_l2_entry_eof_frame(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_mappings(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_hidden_l1_tables_in_locked_windows(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
    }

    /// EOF closure of `remove_l2_entry`: the leaves that need no walk uniqueness, and the shrunk page closure.
    proof fn remove_l2_entry_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.higher.inv(),
            post.va_addr_valid(),
            post.l3_links_l2_wf(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.wf_window_locks(),
            post.page_closure() =~= pre.page_closure().remove(target_l1_p),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger pre.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        Self::remove_l2_entry_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        assert(post.page_closure() =~= pre.page_closure().remove(target_l1_p)) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `remove_l2_entry` for `l3_links_l2_wf`.
    proof fn remove_l2_entry_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.l3_links_l2_wf(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        reveal(WholePageTable::l3_links_l2_wf);
    }

    /// EOF closure of `remove_l2_entry` for `wf_l1`.
    proof fn remove_l2_entry_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_l1(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        reveal(WholePageTable::wf_l1);
    }

    /// EOF closure of `remove_l2_entry` for `disjoint_l2`.
    proof fn remove_l2_entry_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.disjoint_l2(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        reveal(WholePageTable::disjoint_l2);
    }

    /// EOF closure of `remove_l2_entry` for `user_only`.
    proof fn remove_l2_entry_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.user_only(),
    {
        assert forall|p: PageMapPtr, i: L2Index, j: L1Index| #![trigger post.lower.l1_page(p, i).spec_index(j)]
            post.lower.l2_perms.dom().contains(p) && pei_valid(i) && post.lower.l2_page(p).entry_lock(i).l1() is Some
            implies pre.lower.l2_perms.dom().contains(p) && pre.lower.l2_page(p).entry_lock(i).l1() is Some && post.lower.l1_page(p, i).spec_index(j) == pre.lower.l1_page(p, i).spec_index(j) by { reveal(WholePageTable::remove_l2_entry_eof_transition_framing); };
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing); reveal(WholePageTable::user_only);
    }

    /// EOF closure of `remove_l2_entry` for `rwx_upper_level_entries`.
    proof fn remove_l2_entry_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        reveal(WholePageTable::rwx_upper_level_entries);
    }

    /// EOF closure of `remove_l2_entry` for `table_pages_wf`.
    proof fn remove_l2_entry_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.table_pages_wf(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        reveal(WholePageTable::table_pages_wf);
    }

    /// EOF closure of `remove_l2_entry` for `wf_window_locks`.
    proof fn remove_l2_entry_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_window_locks(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        reveal(WholePageTable::wf_window_locks);
    }

    /// EOF closure of `remove_l2_entry`: `wf_l2`.
    proof fn remove_l2_entry_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_entry(target_l2_p, target_l2i).perm.present,
            !pre.lower.l2_entry(target_l2_p, target_l2i).perm.ps,
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_l2(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        assert(post.wf_l2()) by { broadcast use WholePageTable::disjoint_l2_implies_l2_entry_addr_unique_at; reveal(WholePageTable::wf_l2); };
    }

    /// EOF closure of `remove_l2_entry`: the 4K and 2M abstract-mapping leaves.
    proof fn remove_l2_entry_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            forall|i: L1Index| #![trigger pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i) is None,
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); broadcast use PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at, WholePageTable::disjoint_l2_implies_resolve_l2_addr_unique_at; };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); broadcast use PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at; };
    }

    /// EOF closure of `remove_l2_entry`: `tables_reachable_wf`.
    proof fn remove_l2_entry_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); broadcast use PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at; };
    }

    /// EOF closure of `remove_l2_entry`: `hidden_l1_tables_in_locked_windows`. The cleared entry owns no L1 page.
    proof fn remove_l2_entry_eof_hidden_l1_tables_in_locked_windows(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    { reveal(WholePageTable::remove_l2_entry_eof_transition_framing); }

    /// Operation-state summary of `remove_l3_entry`: entry `target_l3i` of the L3 page `target_l3_p` is cleared and the L2
    /// page `target_l2_p` leaves the L2 pages and their reverse index, and its windows leave the window lock map; every other field is
    /// unchanged.
    #[verifier::opaque]
    pub open spec fn remove_l3_entry_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        -> bool {
        &&& post.higher == (PageTableHigher { l3_tables: post.higher.l3_tables, l2_rev_map: post.higher.l2_rev_map, ..pre.higher })
        &&& post.higher.l2_rev_map.view() == pre.higher.l2_rev_map.view().remove(target_l2_p)
        &&& post.higher.l3_tables.view() =~= pre.higher.l3_tables.view().insert(target_l3_p, post.higher.l3_tables.view().spec_index(target_l3_p))
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).is_init()
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().wf()
        &&& forall|i: usize|
            #![trigger pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
            #![trigger post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
            pei_valid(i) && i != target_l3i ==> post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).is_empty()
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, pagetable_window_locks: post.lower.pagetable_window_locks, window_stale_cpus: post.lower.window_stale_cpus, ..pre.lower })
        &&& post.lower.l2_perms == pre.lower.l2_perms.remove(target_l2_p)
        &&& post.lower.pagetable_window_locks == pre.lower.pagetable_window_locks.remove_keys(pre.lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == target_l4i && spec_v2l3index(w.va) == target_l3i))
    }

    /// EOF closure of `remove_l3_entry`: every page-table invariant leaf and the shrunk page closure.
    pub(super) proof fn remove_l3_entry_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l4(target_l4i) is Some,
            pre.spec_held_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index|
                #![trigger pre.lower.l2_page(target_l2_p).entry_lock(i).l1()]
                #![trigger pre.lower.l2_entry(target_l2_p, i)]
                pei_valid(i) ==> pre.lower.l2_page(target_l2_p).entry_lock(i).l1() is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(target_l2_p, i)] pei_valid(i) ==> pre.lower.l2_owner(target_l2_p, i) is None,
            pre.lower.hidden_l1_tables_in_locked_windows(),
            pre.higher.l3_tables.view().dom().contains(target_l3_p),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l2_p),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger pre.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
            post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::remove_l3_entry_eof_resolve_l2_none(pre, target_l4i, target_l3i, target_l2_p);
        Self::remove_l3_entry_eof_higher(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_frame(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_mappings(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_window_locked_by_thread(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_hidden_l1_tables_in_locked_windows(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
    }

    /// EOF closure of `remove_l3_entry`: the big-lock half `higher.inv()`.
    proof fn remove_l3_entry_eof_higher(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l3i),
            pre.higher.l3_tables.view().dom().contains(target_l3_p),
            !pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).perm.ps,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.higher.inv(),
    {
        reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
        assert(post.higher.wf_l4()) by { reveal(PageTableHigher::wf_l4); };
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `remove_l3_entry`: the window-half leaves that read no walk, and the shrunk page closure.
    proof fn remove_l3_entry_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l3i),
            pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).perm.present || pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).perm.kernel_present,
            !pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).perm.ps,
            pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).addr == target_l2_p,
            pre.higher.l3_tables.view().dom().contains(target_l3_p),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.va_addr_valid(),
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l2_p),
    {
        reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); reveal(PageTableHigher::disjoint_l3); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
        assert(post.page_closure() =~= pre.page_closure().remove(target_l2_p)) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `remove_l3_entry`: the 4K and 2M abstract-mapping leaves.
    proof fn remove_l3_entry_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l4(target_l4i) is Some,
            pre.spec_held_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
    {
        Self::remove_l3_entry_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
    }

    /// EOF closure of `remove_l3_entry` for `wf_mapping_4k`.
    proof fn remove_l3_entry_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l4(target_l4i) is Some,
            pre.spec_held_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_4k); broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
    }

    /// EOF closure of `remove_l3_entry` for `wf_mapping_2m`.
    proof fn remove_l3_entry_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l4(target_l4i) is Some,
            pre.spec_held_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_2m); broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
    }

    /// EOF closure of `remove_l3_entry`: `tables_reachable_wf`.
    proof fn remove_l3_entry_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l4(target_l4i) is Some,
            pre.spec_held_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index|
                #![trigger pre.lower.l2_page(target_l2_p).entry_lock(i).l1()]
                #![trigger pre.lower.l2_entry(target_l2_p, i)]
                pei_valid(i) ==> pre.lower.l2_page(target_l2_p).entry_lock(i).l1() is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(target_l2_p, i)] pei_valid(i) ==> pre.lower.l2_owner(target_l2_p, i) is None,
            pre.lower.hidden_l1_tables_in_locked_windows(),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    }

    /// EOF closure of `remove_l3_entry`: `wf_window_locks`.
    proof fn remove_l3_entry_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l4(target_l4i) is Some,
            pre.spec_held_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(target_l2_p, i)] pei_valid(i) ==> pre.lower.l2_owner(target_l2_p, i) is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.wf_window_locks(),
    {
        reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
        reveal(WholePageTable::tables_reachable_wf); reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4); reveal(WholePageTable::l3_links_l2_wf);
        spec_index2va_injective();
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq, spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip;
        reveal(WholePageTable::wf_window_locks);
    }

    /// EOF closure of `remove_l3_entry`: window lock owners. The cleared L3 entry's windows were all unlocked and no
    /// other walk reaches the freed L2 page.
    proof fn remove_l3_entry_eof_window_locked_by_thread(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l4(target_l4i) is Some,
            pre.spec_held_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.lower.l2_owner(target_l2_p, i)] pei_valid(i) ==> pre.lower.l2_owner(target_l2_p, i) is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId|
                #![trigger post.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                #![trigger pre.window_locked_by_thread(l4i, l3i, l2i, thread_id)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.window_locked_by_thread(l4i, l3i, l2i, thread_id) == pre.window_locked_by_thread(l4i, l3i, l2i, thread_id),
    {
        reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
    }

    /// EOF closure of `remove_l3_entry`: no entry of the unlinked L2 page resolves as an L2 link, since none owns an L1 page.
    proof fn remove_l3_entry_eof_resolve_l2_none(pre: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            forall|i: L2Index|
                #![trigger pre.lower.l2_page(target_l2_p).entry_lock(i).l1()]
                #![trigger pre.lower.l2_entry(target_l2_p, i)]
                pei_valid(i) ==> pre.lower.l2_page(target_l2_p).entry_lock(i).l1() is None,
        ensures
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
    {
        reveal(WholePageTable::wf_l2);
        broadcast use PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
    }

    /// EOF closure of `remove_l3_entry`: `hidden_l1_tables_in_locked_windows`. Only the freed L2 page leaves.
    proof fn remove_l3_entry_eof_hidden_l1_tables_in_locked_windows(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.lower.hidden_l1_tables_in_locked_windows(),
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.lower.hidden_l1_tables_in_locked_windows(),
    { reveal(WholePageTable::remove_l3_entry_eof_transition_framing); }

    /// EOF closure of `remove_l2_entry`: the entry no longer holds an L1 page; the rest of the held chain is unchanged.
    pub(super) proof fn remove_l2_entry_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            !pre.lower.l2_entry(target_l2_p, target_l2i).perm.ps,
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            post.spec_held_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|l1i: L1Index| #![trigger post.spec_held_4k_l1(target_l4i, target_l3i, target_l2i, l1i)] pei_valid(l1i) ==> post.spec_held_4k_l1(target_l4i, target_l3i, target_l2i, l1i) is None,
    {
        reveal(WholePageTable::remove_l2_entry_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
        pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(target_l4i, target_l3i);
    }

    /// EOF closure of `remove_l3_entry`: the cleared L3 entry and the freed L2 page leave the held chain; the rest is unchanged.
    pub(super) proof fn remove_l3_entry_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_held_l4(target_l4i) is Some,
            pre.spec_held_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index|
                #![trigger pre.lower.l2_page(target_l2_p).entry_lock(i).l1()]
                #![trigger pre.lower.l2_entry(target_l2_p, i)]
                pei_valid(i) ==> pre.lower.l2_page(target_l2_p).entry_lock(i).l1() is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_held_l3(l4i, l3i) == pre.spec_held_l3(l4i, l3i),
            post.spec_held_l3(target_l4i, target_l3i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_held_1g_l3(l4i, l3i) == pre.spec_held_1g_l3(l4i, l3i),
            post.spec_held_1g_l3(target_l4i, target_l3i) is None,
            forall|l2i: L2Index| #![trigger post.spec_held_2m_l2(target_l4i, target_l3i, l2i)] pei_valid(l2i) ==> post.spec_held_2m_l2(target_l4i, target_l3i, l2i) is None,
            post.lower.l2_perms.dom() == pre.lower.l2_perms.dom().remove(target_l2_p),
            forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_owner(p, i)] post.lower.l2_perms.dom().contains(p) ==> post.lower.l2_owner(p, i) == pre.lower.l2_owner(p, i),
            forall|l4i: L4Index| #![trigger post.spec_resolve_mapping_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_resolve_mapping_l4(l4i) == pre.spec_resolve_mapping_l4(l4i),
    {
        reveal(WholePageTable::remove_l3_entry_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
    }
}
} // verus!
