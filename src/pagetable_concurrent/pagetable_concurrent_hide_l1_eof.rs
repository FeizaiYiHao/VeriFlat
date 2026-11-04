use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `hide_l1_page`: entry `target_l2i` of the L2 page `target_l2_p` now publishes the L1 page
    /// `target_l1_p` with every permission bit clear and keeps owning it; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn hide_l1_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, ..pre.lower })
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != target_l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(target_l2_p).addr() == target_l2_p && post.lower.l2_perms.spec_index(target_l2_p).is_init()
        &&& post.lower.l2_page(target_l2_p).addr() == target_l2_p
        &&& post.lower.l2_page(target_l2_p).wf()
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == target_l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(target_l2_p, target_l2i) == (PageEntry { addr: target_l1_p, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } })
        &&& post.lower.l2_owner(target_l2_p, target_l2i) == pre.lower.l2_owner(target_l2_p, target_l2i)
        &&& post.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() == pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1()
    }

    /// EOF closure of `hide_l1_page`: every page-table invariant leaf, the unchanged page closure, the walks, and the hidden
    /// L1 page's lock.
    pub(super) proof fn hide_l1_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            forall|l1i: L1Index| #![trigger pre.lower.mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, l1i)))]
                pei_valid(l1i) ==> !pre.lower.mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, l1i))),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_owner(target_l2_p, target_l2i) is Write,
            Self::hide_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
            post.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::hide_l1_page_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::hide_l1_page_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::hide_l1_page_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::hide_l1_page_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::hide_l1_page_eof_hidden_l1_tables_in_locked_windows(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        assert(post.higher.inv() && post.va_addr_valid() && post.page_closure() =~= pre.page_closure()) by { reveal(WholePageTable::hide_l1_page_eof_transition_framing); };
    }

    /// EOF closure of `hide_l1_page`: the table-shape leaves of the window half. The hidden entry keeps the L1 page and its
    /// address, so ownership, distinctness, and reachability carry over.
    proof fn hide_l1_page_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::hide_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.tables_reachable_wf(),
            post.wf_window_locks(),
    {
        reveal(WholePageTable::hide_l1_page_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
        assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
    }

    /// EOF-only framing of `hide_l1_page`: the target L2 and 4K walks now miss; every other L2 and 4K walk and every 2M walk
    /// is unchanged.
    proof fn hide_l1_page_eof_resolve_unchanged(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            pre.higher.disjoint_l4(),
            pre.higher.disjoint_l3(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            Self::hide_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l1i: L1Index| #![trigger post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, l1i)] post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, l1i) is None,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
    {
        broadcast use PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at;
        reveal(WholePageTable::hide_l1_page_eof_transition_framing);
    }

    /// EOF closure of `hide_l1_page`: `wf_mapping_4k`. The hidden window maps no 4K page.
    proof fn hide_l1_page_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf_mapping_4k(),
            pre.higher.wf_l4(),
            pre.higher.disjoint_l4(),
            pre.higher.disjoint_l3(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            forall|l1i: L1Index| #![trigger pre.lower.mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, l1i)))]
                pei_valid(l1i) ==> !pre.lower.mapping_4k.dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, l1i))),
            Self::hide_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_mapping_4k(),
    {
        Self::hide_l1_page_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        reveal(WholePageTable::hide_l1_page_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_4k);
    }

    /// EOF closure of `hide_l1_page`: `wf_mapping_2m`.
    proof fn hide_l1_page_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf_mapping_2m(),
            pre.higher.wf_l4(),
            pre.higher.disjoint_l4(),
            pre.higher.disjoint_l3(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            Self::hide_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_mapping_2m(),
    {
        Self::hide_l1_page_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        reveal(WholePageTable::hide_l1_page_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_2m);
    }

    /// EOF closure of `hide_l1_page`: the hidden L1 page sits in a write-locked window.
    proof fn hide_l1_page_eof_hidden_l1_tables_in_locked_windows(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            pre.lower.l2_owner(target_l2_p, target_l2i) is Write,
            Self::hide_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    { reveal(WholePageTable::hide_l1_page_eof_transition_framing); }

    /// Operation-state summary of `unlink_hidden_l1_page`: entry `target_l2i` of the L2 page `target_l2_p` gives up the hidden
    /// L1 page `target_l1_p`, which leaves the L1 pages and their reverse index; the entry word and every other field are
    /// unchanged.
    #[verifier::opaque]
    pub open spec fn unlink_hidden_l1_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
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
        &&& post.lower.l2_entry(target_l2_p, target_l2i) == pre.lower.l2_entry(target_l2_p, target_l2i)
        &&& post.lower.l2_owner(target_l2_p, target_l2i) == pre.lower.l2_owner(target_l2_p, target_l2i)
        &&& post.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is None
    }

    /// EOF closure of `unlink_hidden_l1_page`: every page-table invariant leaf and the shrunk page closure.
    pub(super) proof fn unlink_hidden_l1_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.lower.l2_entry_hides_l1(target_l2_p, target_l2i),
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::unlink_hidden_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l1_p),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::unlink_hidden_l1_page_eof_frame(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::unlink_hidden_l1_page_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::unlink_hidden_l1_page_eof_mappings(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::unlink_hidden_l1_page_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::unlink_hidden_l1_page_eof_hidden_l1_tables_in_locked_windows(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
    }

    /// EOF closure of `unlink_hidden_l1_page`: the leaves that read no walk, and the shrunk page closure.
    proof fn unlink_hidden_l1_page_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::unlink_hidden_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
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
    {
        reveal(WholePageTable::unlink_hidden_l1_page_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
        assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
        assert(post.page_closure() =~= pre.page_closure().remove(target_l1_p)) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `unlink_hidden_l1_page`: `wf_l2`. Every other L1 owner names another page, which stays in the reverse
    /// index.
    proof fn unlink_hidden_l1_page_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_entry_hides_l1(target_l2_p, target_l2i),
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            Self::unlink_hidden_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_l2(),
    {
        reveal(WholePageTable::unlink_hidden_l1_page_eof_transition_framing);
        assert(post.wf_l2()) by { broadcast use WholePageTable::disjoint_l2_implies_l2_entry_addr_unique_at; reveal(WholePageTable::wf_l2); };
    }

    /// EOF closure of `unlink_hidden_l1_page`: the 4K and 2M abstract-mapping leaves. No walk reads the hidden entry.
    proof fn unlink_hidden_l1_page_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.lower.l2_entry_hides_l1(target_l2_p, target_l2i),
            Self::unlink_hidden_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::unlink_hidden_l1_page_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); broadcast use PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at; };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); broadcast use PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at; };
    }

    /// EOF closure of `unlink_hidden_l1_page`: `tables_reachable_wf`. Every L1 page left in the reverse index is owned by
    /// another entry.
    proof fn unlink_hidden_l1_page_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            Self::unlink_hidden_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::unlink_hidden_l1_page_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); broadcast use PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at; };
    }

    /// EOF closure of `unlink_hidden_l1_page`: the entry no longer owns an L1 page.
    proof fn unlink_hidden_l1_page_eof_hidden_l1_tables_in_locked_windows(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index,
        target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            Self::unlink_hidden_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    { reveal(WholePageTable::unlink_hidden_l1_page_eof_transition_framing); }

    /// EOF closure of `hide_l1_page`: the hidden entry still holds its L1 page, now as a placeholder; the rest of the held chain is unchanged.
    pub(super) proof fn hide_l1_page_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::hide_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            post.spec_held_l2(target_l4i, target_l3i, target_l2i) == Some(post.lower.l2_entry(target_l2_p, target_l2i)),
    {
        reveal(WholePageTable::hide_l1_page_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
        pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(target_l4i, target_l3i);
        pre.wf_l2_at(target_l2_p, target_l2i);
    }

    /// EOF closure of `unlink_hidden_l1_page`: the entry no longer holds an L1 page; the rest of the held chain is unchanged.
    pub(super) proof fn unlink_hidden_l1_page_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            Self::unlink_hidden_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
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
        reveal(WholePageTable::unlink_hidden_l1_page_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
        pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(target_l4i, target_l3i);
    }

    /// Operation-state summary of `unlink_unresolvable_l1_page`: entry `target_l2i` of the L2 page `target_l2_p` is published cleared and no
    /// longer owns the L1 page `target_l1_p`, which leaves the L1 reverse index; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn unlink_unresolvable_l1_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr) -> bool {
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

    /// EOF closure of `unlink_unresolvable_l1_page`: every page-table invariant leaf and the shrunk page closure.
    pub(super) proof fn unlink_unresolvable_l1_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is Some,
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            Self::unlink_unresolvable_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l1_p),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::unlink_unresolvable_l1_page_eof_frame(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::unlink_unresolvable_l1_page_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::unlink_unresolvable_l1_page_eof_mappings(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::unlink_unresolvable_l1_page_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        assert(pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows()) by { reveal(WholePageTable::unlink_unresolvable_l1_page_eof_transition_framing); };
    }

    /// EOF closure of `unlink_unresolvable_l1_page`: the leaves that read no walk, and the shrunk page closure.
    proof fn unlink_unresolvable_l1_page_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is Some,
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::unlink_unresolvable_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
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
    {
        reveal(WholePageTable::unlink_unresolvable_l1_page_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
        assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
        assert(post.page_closure() =~= pre.page_closure().remove(target_l1_p)) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `unlink_unresolvable_l1_page`: `wf_l2`.
    proof fn unlink_unresolvable_l1_page_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is Some,
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::unlink_unresolvable_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_l2(),
    {
        reveal(WholePageTable::unlink_unresolvable_l1_page_eof_transition_framing);
        assert(post.wf_l2()) by { broadcast use WholePageTable::disjoint_l2_implies_l2_entry_addr_unique_at; reveal(WholePageTable::wf_l2); };
    }

    /// EOF closure of `unlink_unresolvable_l1_page`: the 4K and 2M abstract-mapping leaves; the target entry resolved nothing before and after.
    proof fn unlink_unresolvable_l1_page_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is Some,
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            Self::unlink_unresolvable_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_mapping_4k(),
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::unlink_unresolvable_l1_page_eof_transition_framing);
        pre.wf_l2_at(target_l2_p, target_l2i);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq; };
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq; };
    }

    /// EOF closure of `unlink_unresolvable_l1_page`: `tables_reachable_wf`.
    proof fn unlink_unresolvable_l1_page_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is Some,
            pre.lower.l2_entry(target_l2_p, target_l2i).addr == target_l1_p,
            pre.lower.l1_rev_map.dom().contains(target_l1_p),
            Self::unlink_unresolvable_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::unlink_unresolvable_l1_page_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    }

    /// EOF closure of `unlink_unresolvable_l1_page`: the entry no longer holds an L1 page; the rest of the held chain is unchanged.
    pub(super) proof fn unlink_unresolvable_l1_page_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_held_l3(target_l4i, target_l3i) is Some,
            pre.spec_held_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            !pre.lower.l2_entry(target_l2_p, target_l2i).perm.ps,
            Self::unlink_unresolvable_l1_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
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
        reveal(WholePageTable::unlink_unresolvable_l1_page_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
    }
}
} // verus!
