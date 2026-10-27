use vstd::prelude::*;
verus! {
use crate::*;
use super::pagetable_spec::*;
use super::entry::*;
use vstd::assert_sets_equal;

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// Operation-state summary of `remove_l4_entry`: the root map's entry `target_l4i` is cleared and the L3 map `target_l3_p`
    /// leaves the L3 maps and their reverse index; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn remove_l4_entry_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr) -> bool {
        &&& post == (Self { l4_table: post.l4_table, l3_rev_map: post.l3_rev_map, l3_tables: post.l3_tables, ..pre })
        &&& post.l3_rev_map.view() == pre.l3_rev_map.view().remove(target_l3_p)
        &&& post.l3_tables.view() == pre.l3_tables.view().remove(target_l3_p)
        &&& post.l4_table.view() =~= pre.l4_table.view().insert(pre.cr3, post.l4_table.view().spec_index(pre.cr3))
        &&& post.l4_table.view().spec_index(pre.cr3).addr() == pre.cr3
        &&& post.l4_table.view().spec_index(pre.cr3).is_init()
        &&& post.l4_table.view().spec_index(pre.cr3).value().wf()
        &&& forall|i: usize| #![trigger pre.l4_table.view().spec_index(pre.cr3).value().spec_index(i)] #![trigger post.l4_table.view().spec_index(pre.cr3).value().spec_index(i)]
            pei_valid(i) && i != target_l4i ==> post.l4_table.view().spec_index(pre.cr3).value().spec_index(i) =~= pre.l4_table.view().spec_index(pre.cr3).value().spec_index(i)
        &&& post.l4_table.view().spec_index(pre.cr3).value().spec_index(target_l4i) =~= (PageEntry { addr: 0, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } })
    }

    /// EOF closure of `remove_l4_entry`: every page-table invariant leaf.
    pub(super) proof fn remove_l4_entry_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            pre.l4_table.view().dom().contains(pre.cr3),
            pre.l3_tables.view().dom().contains(target_l3_p),
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l3_p),
    {
        Self::remove_l4_entry_eof_wf_l4(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_wf_l3(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_wf_l2(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_wf_l1(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_disjoint_l4(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_disjoint_l3(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_disjoint_l2(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_wf_mapping_4k(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_wf_mapping_2m(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_wf_mapping_1g(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_user_only(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_table_pages_wf(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_tables_reachable_wf(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_kernel_entries_wf(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_va_addr_valid_and_pcid_wf(pre, post, target_l4i, target_l3_p);
        Self::remove_l4_entry_eof_page_closure(pre, post, target_l4i, target_l3_p);
    }

    /// EOF closure of `remove_l4_entry`: `wf_l4`.
    proof fn remove_l4_entry_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_l4(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(PageTable::wf_l4); reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `remove_l4_entry`: `wf_l3`.
    proof fn remove_l4_entry_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_l3(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTable::wf_l3); };
    }

    /// EOF closure of `remove_l4_entry`: `wf_l2`.
    proof fn remove_l4_entry_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_l2(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(PageTable::wf_l2); };
    }

    /// EOF closure of `remove_l4_entry`: `wf_l1`.
    proof fn remove_l4_entry_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_l1(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(PageTable::wf_l1); };
    }

    /// EOF closure of `remove_l4_entry`: `disjoint_l4`.
    proof fn remove_l4_entry_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.disjoint_l4(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `remove_l4_entry`: `disjoint_l3`.
    proof fn remove_l4_entry_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.disjoint_l3(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
    }

    /// EOF closure of `remove_l4_entry`: `disjoint_l2`.
    proof fn remove_l4_entry_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.disjoint_l2(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
    }

    /// EOF closure of `remove_l4_entry`: `wf_mapping_4k`.
    proof fn remove_l4_entry_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(PageTable::wf_mapping_4k); reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `remove_l4_entry`: `wf_mapping_2m`.
    proof fn remove_l4_entry_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(PageTable::wf_mapping_2m); reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `remove_l4_entry`: `wf_mapping_1g`.
    proof fn remove_l4_entry_eof_wf_mapping_1g(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.wf_mapping_1g(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.wf_mapping_1g()) by { reveal(PageTable::wf_mapping_1g); reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `remove_l4_entry`: `user_only`.
    proof fn remove_l4_entry_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.user_only(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.user_only()) by { reveal(PageTable::user_only); };
    }

    /// EOF closure of `remove_l4_entry`: `rwx_upper_level_entries`.
    proof fn remove_l4_entry_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `remove_l4_entry`: `table_pages_wf`.
    proof fn remove_l4_entry_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            pre.l4_table.view().dom().contains(pre.cr3),
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.table_pages_wf(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
    }

    /// EOF closure of `remove_l4_entry`: `tables_reachable_wf`.
    proof fn remove_l4_entry_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `remove_l4_entry`: `kernel_entries_wf`.
    proof fn remove_l4_entry_eof_kernel_entries_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.kernel_entries_wf(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert(post.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
    }

    /// EOF closure of `remove_l4_entry`: `va_addr_valid`, `pcid_wf`, and `did_wf`.
    proof fn remove_l4_entry_eof_va_addr_valid_and_pcid_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.va_addr_valid(),
            post.pcid_wf(),
            post.did_wf(),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
    }

    /// EOF closure of `remove_l4_entry`: the shrunk page closure.
    proof fn remove_l4_entry_eof_page_closure(pre: Self, post: Self, target_l4i: L4Index, target_l3_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l3(target_l4i, i) is None,
            forall|i: L3Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_1g_l3(target_l4i, i) is None,
            pre.l4_table.view().dom().contains(pre.cr3),
            pre.l3_tables.view().dom().contains(target_l3_p),
            Self::remove_l4_entry_eof_transition_framing(pre, post, target_l4i, target_l3_p),
        ensures
            post.page_closure() =~= pre.page_closure().remove(target_l3_p),
    {
        reveal(PageTable::remove_l4_entry_eof_transition_framing);
        assert_sets_equal!(post.page_closure() == pre.page_closure().remove(target_l3_p), page_ptr => { reveal(PageTable::table_pages_wf); });
    }
}
} // verus!
