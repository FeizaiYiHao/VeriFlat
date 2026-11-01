use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `unmap_4k_page_kernel`: entry `target_l1i` of the L1 map `target_l1_p` is cleared and
    /// the 4K mapping of its address is removed; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn unmap_4k_page_kernel_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr) -> bool {
        let l2_p = pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr;
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, mapping_4k: post.lower.mapping_4k, ..pre.lower })
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(l2_p).addr() == l2_p && post.lower.l2_perms.spec_index(l2_p).is_init()
        &&& post.lower.l2_page(l2_p).addr() == l2_p
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(l2_p, target_l2i) == pre.lower.l2_entry(l2_p, target_l2i)
        &&& post.lower.l2_owner(l2_p, target_l2i) == pre.lower.l2_owner(l2_p, target_l2i)
        &&& pre.lower.l2_page(l2_p).entry_lock(target_l2i).l1() is Some && pre.lower.l1_perm(l2_p, target_l2i).addr() == target_l1_p
        &&& post.lower.l2_page(l2_p).entry_lock(target_l2i).l1() is Some
        &&& post.lower.l1_perm(l2_p, target_l2i).addr() == target_l1_p
        &&& post.lower.l1_perm(l2_p, target_l2i).is_init()
        &&& post.lower.l1_page(l2_p, target_l2i).wf()
        &&& forall|p: PageMapPtr, i: L2Index, j: L1Index| #![trigger post.lower.l1_page(p, i).spec_index(j)]
            p == l2_p && i == target_l2i && pei_valid(j) && j != target_l1i ==> post.lower.l1_page(p, i).spec_index(j) =~= pre.lower.l1_page(p, i).spec_index(j)
        &&& post.lower.l1_page(l2_p, target_l2i).spec_index(target_l1i).is_empty()
        &&& post.lower.mapping_4k == pre.lower.mapping_4k.remove(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)))
    }

    /// EOF closure of `unmap_4k_page_kernel`: every page-table invariant leaf, the unchanged page closure, and the
    /// cleared walk.
    pub(super) proof fn unmap_4k_page_kernel_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            pre.mapping_4k().dom().contains(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))),
            pre.mapping_4k().spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))).present == false,
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
            post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
    {
        Self::unmap_4k_page_kernel_eof_frame(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
    }

    /// EOF closure of `unmap_4k_page_kernel`: the leaves that read no L1 entry and no 4K mapping value.
    proof fn unmap_4k_page_kernel_eof_frame(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.higher.inv(),
            post.va_addr_valid(),
            post.wf_l3(),
            post.wf_l2(),
            post.disjoint_l2(),
            post.wf_mapping_2m(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.wf_window_locks(),
            post.page_closure() =~= pre.page_closure(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        Self::unmap_4k_page_kernel_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
        Self::unmap_4k_page_kernel_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `wf_l3`.
    proof fn unmap_4k_page_kernel_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l3(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::wf_l3);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `wf_l2`.
    proof fn unmap_4k_page_kernel_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l2(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::wf_l2);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `disjoint_l2`.
    proof fn unmap_4k_page_kernel_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.disjoint_l2(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::disjoint_l2);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `wf_mapping_2m`.
    proof fn unmap_4k_page_kernel_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_2m);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `rwx_upper_level_entries`.
    proof fn unmap_4k_page_kernel_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::rwx_upper_level_entries);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `table_pages_wf`.
    proof fn unmap_4k_page_kernel_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.table_pages_wf(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::table_pages_wf);
    }

    /// EOF closure of `unmap_4k_page_kernel` for `wf_window_locks`.
    proof fn unmap_4k_page_kernel_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_window_locks(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        reveal(WholePageTable::wf_window_locks);
    }

    /// EOF closure of `unmap_4k_page_kernel`: the L1 leaves `wf_l1` and `user_only`.
    proof fn unmap_4k_page_kernel_eof_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_l1(),
            post.user_only(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `wf_mapping_4k` and the cleared walk.
    proof fn unmap_4k_page_kernel_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pei_valid(target_l1i),
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i)->0.addr == target_l1_p,
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.wf_mapping_4k(),
            post.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) is None,
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        post.resolve_l2_unchanged(&pre);
        assert(post.wf_mapping_4k()) by {
            reveal(WholePageTable::wf_mapping_4k);
            spec_index2va_injective();
            broadcast use WholePageTable::resolve_l2_addr_unique_at, WholePageTable::resolve_l2_target_exists;
        };
    }

    /// EOF closure of `unmap_4k_page_kernel`: `tables_reachable_wf`.
    proof fn unmap_4k_page_kernel_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l1i: L1Index,
        target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            Self::unmap_4k_page_kernel_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l1i, target_l1_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); };
    }
}
} // verus!
