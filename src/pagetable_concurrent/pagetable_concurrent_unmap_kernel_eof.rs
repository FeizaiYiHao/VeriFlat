use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
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
        reveal(PageTableC::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
        assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
        assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
        assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
        assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); };
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
        reveal(PageTableC::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(post.user_only()) by { reveal(PageTableC::user_only); };
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
        reveal(PageTableC::unmap_4k_page_kernel_eof_transition_framing);
        post.resolve_l2_unchanged(&pre);
        assert(post.wf_mapping_4k()) by {
            reveal(PageTableC::wf_mapping_4k);
            spec_index2va_injective();
            broadcast use PageTableC::resolve_l2_addr_unique_at, PageTableC::resolve_l2_target_exists;
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
        reveal(PageTableC::unmap_4k_page_kernel_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); };
    }
}
} // verus!
