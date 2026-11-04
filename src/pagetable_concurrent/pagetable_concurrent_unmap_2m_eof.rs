use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
    /// Operation-state summary of `unmap_2m_page_user_view`: entry `target_l2i` of the L2 page `target_l2_p` loses its present
    /// bit and the 2M mapping of its address is kept with `present` cleared; the big-lock payload and every other window-half
    /// field are unchanged.
    #[verifier::opaque]
    pub open spec fn unmap_2m_page_user_view_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, mapping_2m: post.lower.mapping_2m, ..pre.lower })
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != target_l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(target_l2_p).addr() == target_l2_p && post.lower.l2_perms.spec_index(target_l2_p).is_init()
        &&& post.lower.l2_page(target_l2_p).addr() == target_l2_p
        &&& post.lower.l2_page(target_l2_p).wf()
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == target_l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(target_l2_p, target_l2i)
            == (PageEntry { perm: PageEntryPerm { present: false, ..pre.lower.l2_entry(target_l2_p, target_l2i).perm }, ..pre.lower.l2_entry(target_l2_p, target_l2i) })
        &&& post.lower.l2_owner(target_l2_p, target_l2i) == pre.lower.l2_owner(target_l2_p, target_l2i)
        &&& post.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() == pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1()
        &&& post.lower.mapping_2m == pre.lower.mapping_2m.insert(spec_index2va((target_l4i, target_l3i, target_l2i, 0)),
            MapEntry { present: false, ..pre.lower.mapping_2m.spec_index(spec_index2va((target_l4i, target_l3i, target_l2i, 0))) })
    }

    /// EOF closure of `unmap_2m_page_user_view`: every page-table invariant leaf and the unchanged page closure.
    pub(super) proof fn unmap_2m_page_user_view_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_owner(target_l2_p, target_l2i) is Write,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        pre.wf_l2_at(target_l2_p, target_l2i);
        Self::unmap_2m_page_user_view_eof_va_addr_valid(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        Self::unmap_2m_page_user_view_eof_hidden_l1_tables_in_locked_windows(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        assert(post.higher.inv() && post.page_closure() =~= pre.page_closure()) by { reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing); };
    }

    /// EOF closure of `unmap_2m_page_user_view`: `va_addr_valid`.
    proof fn unmap_2m_page_user_view_eof_va_addr_valid(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.va_addr_valid(),
            pre.wf_mapping_2m(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is Some,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.va_addr_valid(),
    {
        pre.wf_mapping_2m_at(target_l4i, target_l3i, target_l2i);
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `wf_l3`.
    proof fn unmap_2m_page_user_view_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.wf_l3(),
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.wf_l3(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::wf_l3);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `wf_l2`.
    proof fn unmap_2m_page_user_view_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.wf_l2(),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.wf_l2(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::wf_l2);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `wf_l1`.
    proof fn unmap_2m_page_user_view_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.wf_l1(),
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.wf_l1(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::wf_l1);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `disjoint_l2`.
    proof fn unmap_2m_page_user_view_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.disjoint_l2(),
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.disjoint_l2(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::disjoint_l2);
    }

    /// EOF-only framing of `unmap_2m_page_user_view`: the L2 and 4K walks are unchanged, and so is every 2M walk except the
    /// target one.
    proof fn unmap_2m_page_user_view_eof_resolve_unchanged(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            pre.higher.disjoint_l4(),
            pre.higher.disjoint_l3(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is Some,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
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
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `wf_mapping_4k`.
    proof fn unmap_2m_page_user_view_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
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
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is Some,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.wf_mapping_4k(),
    {
        Self::unmap_2m_page_user_view_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_4k);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `wf_mapping_2m`.
    proof fn unmap_2m_page_user_view_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
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
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is Some,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.wf_mapping_2m(),
    {
        Self::unmap_2m_page_user_view_eof_resolve_unchanged(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p);
        pre.wf_mapping_2m_at(target_l4i, target_l3i, target_l2i);
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::wf_mapping_2m);
        spec_index2va_injective();
    }

    /// EOF closure of `unmap_2m_page_user_view`: `user_only`.
    proof fn unmap_2m_page_user_view_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.user_only(),
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.user_only(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::user_only);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `rwx_upper_level_entries`.
    proof fn unmap_2m_page_user_view_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.rwx_upper_level_entries(),
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::rwx_upper_level_entries);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `table_pages_wf`.
    proof fn unmap_2m_page_user_view_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.table_pages_wf(),
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.table_pages_wf(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::table_pages_wf);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `tables_reachable_wf`.
    proof fn unmap_2m_page_user_view_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.tables_reachable_wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::tables_reachable_wf);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `wf_window_locks`.
    proof fn unmap_2m_page_user_view_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.wf_window_locks(),
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            post.wf_window_locks(),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        reveal(WholePageTable::wf_window_locks);
    }

    /// EOF closure of `unmap_2m_page_user_view`: `hidden_l1_tables_in_locked_windows`. The target window stays write-locked.
    proof fn unmap_2m_page_user_view_eof_hidden_l1_tables_in_locked_windows(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.lower.l2_owner(target_l2_p, target_l2i) is Write,
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    { reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing); }

    /// EOF closure of `unmap_2m_page_user_view`: the target 2M leaf stays held with its present bit clear; the rest of the held chain is unchanged.
    pub(super) proof fn unmap_2m_page_user_view_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.lower.l2_perms.dom().contains(target_l2_p),
            Self::unmap_2m_page_user_view_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            post.spec_held_2m_l2(target_l4i, target_l3i, target_l2i) == Some(post.lower.l2_entry(target_l2_p, target_l2i)),
    {
        reveal(WholePageTable::unmap_2m_page_user_view_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
        pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(target_l4i, target_l3i);
        pre.wf_l2_at(target_l2_p, target_l2i);
    }
}
} // verus!
