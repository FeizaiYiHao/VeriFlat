use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    /// Operation-state summary of `map_2m_page`: entry `target_l2i` of the L2 page `target_l2_p` now maps `target_entry` as a 2M
    /// page and the 2M mapping records it at that address; the big-lock payload and every other window-half field are unchanged.
    #[verifier::opaque]
    pub open spec fn map_2m_page_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, mapping_2m: post.lower.mapping_2m, ..pre.lower })
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != target_l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(target_l2_p).addr() == target_l2_p && post.lower.l2_perms.spec_index(target_l2_p).is_init()
        &&& post.lower.l2_page(target_l2_p).addr() == target_l2_p
        &&& post.lower.l2_page(target_l2_p).wf()
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == target_l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(target_l2_p, target_l2i) == (PageEntry { addr: target_entry.addr,
            perm: PageEntryPerm { present: true, ps: true, write: target_entry.write, execute_disable: target_entry.execute_disable, user: true, kernel_present: true } })
        &&& post.lower.l2_owner(target_l2_p, target_l2i) == pre.lower.l2_owner(target_l2_p, target_l2i)
        &&& post.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() == pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1()
        &&& post.lower.mapping_2m == pre.lower.mapping_2m.insert(spec_index2va((target_l4i, target_l3i, target_l2i, 0)), target_entry)
    }

    /// EOF closure of `map_2m_page`: every page-table invariant leaf.
    pub(super) proof fn map_2m_page_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0))),
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf(),
    {
        Self::map_2m_page_eof_va_addr_valid(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        Self::map_2m_page_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        assert(post.higher.inv()) by { reveal(PageTableC::map_2m_page_eof_transition_framing); };
    }

    /// EOF closure of `map_2m_page`: `va_addr_valid`.
    proof fn map_2m_page_eof_va_addr_valid(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.va_addr_valid(),
            page_ptr_2m_valid(target_entry.addr),
            page_table_key_2m_valid::<TABLE_TYPE>(spec_index2va((target_l4i, target_l3i, target_l2i, 0))),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.va_addr_valid(),
    { reveal(PageTableC::map_2m_page_eof_transition_framing); }

    /// EOF closure of `map_2m_page`: `wf_l3`.
    proof fn map_2m_page_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf_l3(),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_l3(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::wf_l3);
    }


    /// EOF closure of `map_2m_page`: `wf_l2`.
    proof fn map_2m_page_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf_l2(),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_l2(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::wf_l2);
    }

    /// EOF closure of `map_2m_page`: `wf_l1`.
    proof fn map_2m_page_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf_l1(),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_l1(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::wf_l1);
    }

    /// EOF closure of `map_2m_page`: `disjoint_l2`.
    proof fn map_2m_page_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.disjoint_l2(),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.disjoint_l2(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::disjoint_l2);
    }

    /// EOF-only framing of `map_2m_page`: the L2 and 4K walks are unchanged, and so is every 2M walk except the target one.
    proof fn map_2m_page_eof_resolve_unchanged(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.higher.wf_l4(),
            pre.higher.disjoint_l4(),
            pre.higher.disjoint_l3(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger post.spec_resolve_mapping_l2(l4i, l3i, l2i)]
                post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_resolve_mapping_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)]
                post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                    ==> post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i)]
                post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i)
                    ==> post.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i),
    {
        broadcast use PageTableHigher::resolve_l3_addr_unique_at;
        reveal(PageTableC::map_2m_page_eof_transition_framing);
    }

    /// EOF closure of `map_2m_page`: `wf_mapping_4k`.
    proof fn map_2m_page_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
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
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_mapping_4k(),
    {
        Self::map_2m_page_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::wf_mapping_4k);
    }

    /// EOF closure of `map_2m_page`: `wf_mapping_2m`.
    proof fn map_2m_page_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
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
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            target_entry.present,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_mapping_2m(),
    {
        Self::map_2m_page_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry);
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::wf_mapping_2m);
        spec_index2va_injective();
    }

    /// EOF closure of `map_2m_page`: `user_only`.
    proof fn map_2m_page_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.user_only(),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.user_only(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::user_only);
    }

    /// EOF closure of `map_2m_page`: `rwx_upper_level_entries`.
    proof fn map_2m_page_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.rwx_upper_level_entries(),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::rwx_upper_level_entries);
    }

    /// EOF closure of `map_2m_page`: `table_pages_wf`.
    proof fn map_2m_page_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.table_pages_wf(),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.table_pages_wf(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::table_pages_wf);
    }

    /// EOF closure of `map_2m_page`: `tables_reachable_wf`.
    proof fn map_2m_page_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.tables_reachable_wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::tables_reachable_wf);
    }

    /// EOF closure of `map_2m_page`: `wf_window_locks`.
    proof fn map_2m_page_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_entry: MapEntry)
        requires
            pre.wf_window_locks(),
            Self::map_2m_page_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, target_entry),
        ensures
            post.wf_window_locks(),
    {
        reveal(PageTableC::map_2m_page_eof_transition_framing);
        reveal(PageTableC::wf_window_locks);
    }
}
} // verus!
