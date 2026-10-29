use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    /// Operation-state summary of `unmap_4k_page_user_view`: entry `target_l1i` of the L1 map `target_l1_p` loses its
    /// present bit and the 4K mapping of its address is kept with `present` cleared; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn unmap_4k_page_user_view_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l1_tables: post.lower.l1_tables, mapping_4k: post.lower.mapping_4k, ..pre.lower })
        &&& post.lower.l1_tables.dom() == pre.lower.l1_tables.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l1_tables.spec_index(p)] pre.lower.l1_tables.dom().contains(p) && p != target_l1_p ==> post.lower.l1_tables.spec_index(p) == pre.lower.l1_tables.spec_index(p)
        &&& post.lower.l1_tables.spec_index(target_l1_p).addr() == target_l1_p
        &&& post.lower.l1_tables.spec_index(target_l1_p).is_init()
        &&& post.lower.l1_tables.spec_index(target_l1_p).value().wf()
        &&& forall|i: usize|
            #![trigger post.lower.l1_tables.spec_index(target_l1_p).value().spec_index(i)]
            pei_valid(i) && i != target_l1i ==> post.lower.l1_tables.spec_index(target_l1_p).value().spec_index(i) =~= pre.lower.l1_tables.spec_index(target_l1_p).value().spec_index(i)
        &&& post.lower.l1_tables.spec_index(target_l1_p).value().spec_index(target_l1i)
            =~= (PageEntry { perm: PageEntryPerm { present: false, ..pre.lower.l1_tables.spec_index(target_l1_p).value().spec_index(target_l1i).perm }, ..pre.lower.l1_tables.spec_index(target_l1_p).value().spec_index(target_l1i) })
        &&& post.lower.mapping_4k == pre.lower.mapping_4k.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            MapEntry { present: false, ..pre.lower.mapping_4k.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))) })
    }

    /// EOF closure of `unmap_4k_page_user_view`: every page-table invariant leaf and the unchanged page closure.
    pub(super) proof fn unmap_4k_page_user_view_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is Some || pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
    {
        assert(pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)))) by { reveal(PageTableC::wf_mapping_4k); };
        Self::unmap_4k_page_user_view_eof_frame(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_user_view_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
    }

    /// EOF closure of `unmap_4k_page_user_view`: the leaves that read no L1 entry and no 4K mapping value.
    proof fn unmap_4k_page_user_view_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l1i),
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.higher.inv(),
            post.va_addr_valid(),
            post.wf_l3(),
            post.l2_tokens_paired(),
            post.wf_l2(),
            post.disjoint_l2(),
            post.wf_mapping_2m(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.wf_window_locks(),
            post.page_closure() =~= pre.page_closure(),
    {
        reveal(PageTableC::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
        assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
        assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
        assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
        assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
        assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: the L1 leaves `wf_l1` and `user_only`.
    proof fn unmap_4k_page_user_view_eof_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pei_valid(target_l1i),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l1(),
            post.user_only(),
    {
        reveal(PageTableC::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(post.user_only()) by { reveal(PageTableC::user_only); };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `wf_mapping_4k`.
    proof fn unmap_4k_page_user_view_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(PageTableC::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.wf_mapping_4k()) by {
            reveal(PageTableC::wf_mapping_4k);
            spec_index2va_injective();
            post.resolve_l2_unchanged(&pre);
            broadcast use PageTableC::resolve_l2_addr_unique_at, PageTableC::resolve_l2_target_exists;
        };
    }

    /// EOF closure of `unmap_4k_page_user_view`: `tables_reachable_wf`.
    proof fn unmap_4k_page_user_view_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTableC::unmap_4k_page_user_view_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); };
    }
}
} // verus!
