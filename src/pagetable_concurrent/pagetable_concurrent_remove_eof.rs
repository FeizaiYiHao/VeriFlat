use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    /// Operation-state summary of `remove_l2_entry`: entry `target_l2i` of the L2 page `target_l2_p` is cleared and the
    /// L1 page `target_l1_p` leaves the L1 pages and their reverse index; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn remove_l2_entry_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_ghost: post.lower.l2_ghost, l1_rev_map: post.lower.l1_rev_map, l1_tables: post.lower.l1_tables, ..pre.lower })
        &&& post.lower.l1_rev_map == pre.lower.l1_rev_map.remove(target_l1_p)
        &&& post.lower.l1_tables == pre.lower.l1_tables.remove(target_l1_p)
        &&& post.lower.l2_ghost == pre.lower.l2_ghost.insert(target_l2_p, post.lower.l2_page(target_l2_p))
        &&& post.lower.l2_ghost.dom() =~= pre.lower.l2_ghost.dom()
        &&& post.lower.l2_page(target_l2_p).addr() == target_l2_p
        &&& post.lower.l2_page(target_l2_p).wf()
        &&& forall|i: usize|
            #![trigger post.lower.l2_page(target_l2_p).spec_index(i)]
            pei_valid(i) && i != target_l2i ==> post.lower.l2_page(target_l2_p).spec_index(i) =~= pre.lower.l2_page(target_l2_p).spec_index(i)
        &&& post.lower.l2_page(target_l2_p).spec_index(target_l2i).is_empty()
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
            pre.lower.l1_tables.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l1_p),
    {
        Self::remove_l2_entry_eof_frame(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_mappings(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
        Self::remove_l2_entry_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p);
    }

    /// EOF closure of `remove_l2_entry`: the leaves that need no walk uniqueness, and the shrunk page closure.
    proof fn remove_l2_entry_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l1_tables.dom().contains(target_l1_p),
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.higher.inv(), post.va_addr_valid(), post.wf_l3(), post.l2_tokens_paired(), post.wf_l1(), post.disjoint_l2(), post.user_only(),
            post.rwx_upper_level_entries(), post.table_pages_wf(), post.wf_window_locks(),
            post.page_closure() =~= pre.page_closure().remove(target_l1_p),
    {
        reveal(PageTableC::remove_l2_entry_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
        assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
        assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
        assert(post.user_only()) by { reveal(PageTableC::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
        assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); };
        assert(post.page_closure() =~= pre.page_closure().remove(target_l1_p)) by { reveal(PageTableC::table_pages_wf); };
    }

    /// EOF closure of `remove_l2_entry`: `wf_l2`.
    proof fn remove_l2_entry_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l2i),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_page(target_l2_p).spec_index(target_l2i).perm.present,
            !pre.lower.l2_page(target_l2_p).spec_index(target_l2i).perm.ps,
            pre.lower.l2_page(target_l2_p).spec_index(target_l2i).addr == target_l1_p,
            Self::remove_l2_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_l1_p),
        ensures
            post.wf_l2(),
    {
        reveal(PageTableC::remove_l2_entry_eof_transition_framing);
        assert(post.wf_l2()) by { broadcast use PageTableC::l2_entry_addr_unique_at; reveal(PageTableC::wf_l2); };
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
            post.wf_mapping_4k(), post.wf_mapping_2m(),
    {
        reveal(PageTableC::remove_l2_entry_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); broadcast use PageTableHigher::resolve_l3_addr_unique_at, PageTableC::resolve_l2_addr_unique_at; };
        assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); broadcast use PageTableHigher::resolve_l3_addr_unique_at; };
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
        reveal(PageTableC::remove_l2_entry_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); broadcast use PageTableHigher::resolve_l3_addr_unique_at; };
    }

    /// Operation-state summary of `remove_l3_entry`: entry `target_l3i` of the L3 page `target_l3_p` is cleared and the L2
    /// page `target_l2_p` leaves the L2 pages, both of their tokens, and their reverse index; every other field is
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
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, l2_ghost: post.lower.l2_ghost, l2_lock: post.lower.l2_lock, ..pre.lower })
        &&& post.lower.l2_perms == pre.lower.l2_perms.remove(target_l2_p)
        &&& post.lower.l2_ghost == pre.lower.l2_ghost.remove(target_l2_p)
        &&& post.lower.l2_lock == pre.lower.l2_lock.remove(target_l2_p)
    }

    /// EOF closure of `remove_l3_entry`: every page-table invariant leaf and the shrunk page closure.
    pub(super) proof fn remove_l3_entry_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.lower.l2_lock_of(target_l2_p).lock_state(i)] pei_valid(i) ==> pre.lower.l2_lock_of(target_l2_p).lock_state(i) is None,
            pre.higher.l3_tables.view().dom().contains(target_l3_p),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l2_p),
    {
        Self::remove_l3_entry_eof_higher(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_frame(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_mappings(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
        Self::remove_l3_entry_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p);
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
        reveal(PageTableC::remove_l3_entry_eof_transition_framing);
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
            pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).perm.present,
            !pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).perm.ps,
            pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i).addr == target_l2_p,
            pre.higher.l3_tables.view().dom().contains(target_l3_p),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.va_addr_valid(), post.wf_l3(), post.l2_tokens_paired(), post.wf_l2(), post.wf_l1(), post.disjoint_l2(), post.user_only(),
            post.rwx_upper_level_entries(), post.table_pages_wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l2_p),
    {
        reveal(PageTableC::remove_l3_entry_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); reveal(PageTableHigher::disjoint_l3); };
        assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
        assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
        assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
        assert(post.user_only()) by { reveal(PageTableC::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
        assert(post.page_closure() =~= pre.page_closure().remove(target_l2_p)) by { reveal(PageTableC::table_pages_wf); };
    }

    /// EOF closure of `remove_l3_entry`: the 4K and 2M abstract-mapping leaves.
    proof fn remove_l3_entry_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.wf_mapping_4k(), post.wf_mapping_2m(),
    {
        reveal(PageTableC::remove_l3_entry_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); broadcast use PageTableHigher::resolve_l3_addr_unique_at; };
        assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); broadcast use PageTableHigher::resolve_l3_addr_unique_at; };
    }

    /// EOF closure of `remove_l3_entry`: `tables_reachable_wf`.
    proof fn remove_l3_entry_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![trigger pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i)] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTableC::remove_l3_entry_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); broadcast use PageTableHigher::resolve_l3_addr_unique_at; };
    }

    /// EOF closure of `remove_l3_entry`: `wf_window_locks`.
    proof fn remove_l3_entry_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            forall|i: L2Index| #![trigger pre.lower.l2_lock_of(target_l2_p).lock_state(i)] pei_valid(i) ==> pre.lower.l2_lock_of(target_l2_p).lock_state(i) is None,
            Self::remove_l3_entry_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, target_l2_p),
        ensures
            post.wf_window_locks(),
    {
        reveal(PageTableC::remove_l3_entry_eof_transition_framing);
        assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); broadcast use spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip; };
    }
}
} // verus!
