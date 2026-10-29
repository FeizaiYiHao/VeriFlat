use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    /// Operation-state summary of `map_4k_page`: entry `target_l1i` of the L1 map `target_l1_p` now maps `target_entry`
    /// and the 4K mapping records it at that address; the big-lock payload and every other window-half field are unchanged.
    #[verifier::opaque]
    pub open spec fn map_4k_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr, target_entry: MapEntry) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l1_tables: post.lower.l1_tables, mapping_4k: post.lower.mapping_4k, ..pre.lower })
        &&& post.lower.l1_tables.dom() == pre.lower.l1_tables.dom()
        &&& post.lower.l1_tables =~= pre.lower.l1_tables.insert(target_l1_p, post.lower.l1_tables.spec_index(target_l1_p))
        &&& post.lower.l1_tables.spec_index(target_l1_p).addr() == target_l1_p
        &&& post.lower.l1_tables.spec_index(target_l1_p).is_init()
        &&& post.lower.l1_tables.spec_index(target_l1_p).value().wf()
        &&& forall|i: usize|
            #![trigger post.lower.l1_tables.spec_index(target_l1_p).value().spec_index(i)]
            pei_valid(i) && i != target_l1i ==> post.lower.l1_tables.spec_index(target_l1_p).value().spec_index(i) =~= pre.lower.l1_tables.spec_index(target_l1_p).value().spec_index(i)
        &&& post.lower.l1_tables.spec_index(target_l1_p).value().spec_index(target_l1i) =~= (PageEntry { addr: target_entry.addr,
            perm: PageEntryPerm { present: true, ps: false, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } })
        &&& post.lower.mapping_4k == pre.lower.mapping_4k.insert(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)), target_entry)
    }

    /// EOF closure of `map_4k_page`: every page-table invariant leaf.
    pub(super) proof fn map_4k_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.lower.l1_tables.dom().contains(target_l1_p),
            page_ptr_valid(target_entry.addr),
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf(),
    {
        Self::map_4k_page_eof_va_addr_valid(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_l2_tokens_paired(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        Self::map_4k_page_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        assert(post.higher.inv()) by { reveal(PageTableC::map_4k_page_eof_transition_framing); };
    }

    /// EOF closure of `map_4k_page`: `va_addr_valid`.
    proof fn map_4k_page_eof_va_addr_valid(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.va_addr_valid(),
            page_table_key_4k_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            page_ptr_valid(target_entry.addr),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.va_addr_valid(),
    { reveal(PageTableC::map_4k_page_eof_transition_framing); }

    /// EOF closure of `map_4k_page`: `wf_l3`.
    proof fn map_4k_page_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.wf_l3(),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l3(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::wf_l3);
    }

    /// EOF closure of `map_4k_page`: `l2_tokens_paired`.
    proof fn map_4k_page_eof_l2_tokens_paired(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.l2_tokens_paired(),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.l2_tokens_paired(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::l2_tokens_paired);
    }

    /// EOF closure of `map_4k_page`: `wf_l2`.
    proof fn map_4k_page_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.wf_l2(),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l2(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::wf_l2);
    }

    /// EOF closure of `map_4k_page`: `wf_l1`.
    proof fn map_4k_page_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.wf_l1(),
            pre.lower.l1_tables.dom().contains(target_l1_p),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_l1(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::wf_l1);
    }

    /// EOF closure of `map_4k_page`: `disjoint_l2`.
    proof fn map_4k_page_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.disjoint_l2(),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.disjoint_l2(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::disjoint_l2);
    }

    /// EOF-only framing of `map_4k_page`: the 2M and L2 walks are unchanged, and so is every 4K walk except the target one.
    proof fn map_4k_page_eof_resolve_unchanged(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.higher.wf_l4(),
            pre.wf_l3(),
            pre.higher.disjoint_l4(),
            pre.higher.disjoint_l3(),
            pre.disjoint_l2(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)] post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && (l4i, l3i, l2i, l1i) != (target_l4i, target_l3i, target_l2i, target_l1i)
                    ==> post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
    {
        broadcast use PageTableC::resolve_l2_addr_unique_at;
        reveal(PageTableC::map_4k_page_eof_transition_framing);
    }

    /// EOF closure of `map_4k_page`: `wf_mapping_4k`.
    proof fn map_4k_page_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.higher.wf_l4(),
            pre.wf_l3(),
            pre.higher.disjoint_l4(),
            pre.higher.disjoint_l3(),
            pre.disjoint_l2(),
            pre.wf_mapping_4k(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            target_entry.present,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_mapping_4k(),
    {
        Self::map_4k_page_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::wf_mapping_4k);
        spec_index2va_injective();
    }

    /// EOF closure of `map_4k_page`: `wf_mapping_2m`.
    proof fn map_4k_page_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.higher.wf_l4(),
            pre.wf_l3(),
            pre.higher.disjoint_l4(),
            pre.higher.disjoint_l3(),
            pre.disjoint_l2(),
            pre.wf_mapping_2m(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_mapping_2m(),
    {
        Self::map_4k_page_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry);
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::wf_mapping_2m);
    }

    /// EOF closure of `map_4k_page`: `user_only`.
    proof fn map_4k_page_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.user_only(),
            pre.lower.l1_tables.dom().contains(target_l1_p),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.user_only(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::user_only);
    }

    /// EOF closure of `map_4k_page`: `rwx_upper_level_entries`.
    proof fn map_4k_page_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.rwx_upper_level_entries(),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::rwx_upper_level_entries);
    }

    /// EOF closure of `map_4k_page`: `table_pages_wf`.
    proof fn map_4k_page_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.table_pages_wf(),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.table_pages_wf(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::table_pages_wf);
    }

    /// EOF closure of `map_4k_page`: `tables_reachable_wf`.
    proof fn map_4k_page_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.tables_reachable_wf(),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::tables_reachable_wf);
    }

    /// EOF closure of `map_4k_page`: `wf_window_locks`.
    proof fn map_4k_page_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr,
        target_entry: MapEntry)
        requires
            pre.wf_window_locks(),
            Self::map_4k_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p, target_entry),
        ensures
            post.wf_window_locks(),
    {
        reveal(PageTableC::map_4k_page_eof_transition_framing);
        reveal(PageTableC::wf_window_locks);
    }
}
} // verus!
