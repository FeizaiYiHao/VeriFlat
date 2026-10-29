use vstd::prelude::*;
verus! {
use crate::*;
use super::pagetable_spec::*;
use super::entry::*;

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// EOF closure of `remove_l2_entry`: table-structure leaves and the shrunk page closure.
    pub(super) proof fn remove_l2_entry_eof_tables(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).unwrap().addr == target_l1_p,
            forall|i: L1Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i) is None,
            pre.l2_tables.view().dom().contains(target_l2_p),
            pre.l1_tables.view().dom().contains(target_l1_p),
            post == (Self { l2_tables: post.l2_tables, l1_rev_map: post.l1_rev_map, l1_tables: post.l1_tables, ..pre }),
            post.l1_rev_map.view() == pre.l1_rev_map.view().remove(target_l1_p),
            post.l1_tables.view() == pre.l1_tables.view().remove(target_l1_p),
            post.l2_tables.view() =~= pre.l2_tables.view().insert(target_l2_p, post.l2_tables.view().spec_index(target_l2_p)),
            post.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p,
            post.l2_tables.view().spec_index(target_l2_p).is_init(),
            post.l2_tables.view().spec_index(target_l2_p).value().wf(),
            forall|i: usize|
                #![trigger pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
                #![trigger post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
                pei_valid(i) && i != target_l2i ==> post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i) =~= pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i),
            post.l2_tables.view().spec_index(target_l2_p).value().spec_index(target_l2i) =~= (PageEntry { addr: 0, perm: PageEntryPerm {
                present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } }),
        ensures
            post.wf_l4(),
            post.wf_l3(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l4(),
            post.disjoint_l3(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.kernel_entries_wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l1_p),
    {
        assert(post.wf_l4()) by { reveal(PageTable::wf_l4); };
        assert(post.wf_l3()) by { reveal(PageTable::wf_l3); };
        assert(post.wf_l2()) by { broadcast use PageTable::l2_entry_addr_unique_at; reveal(PageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(PageTable::wf_l1); };
        assert(post.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(post.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(post.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(PageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(post.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
        assert(post.page_closure() =~= pre.page_closure().remove(target_l1_p)) by { reveal(PageTable::table_pages_wf); };
    }

    /// EOF closure of `remove_l2_entry`: 4K abstract-mapping leaf.
    pub(super) proof fn remove_l2_entry_eof_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).unwrap().addr == target_l1_p,
            forall|i: L1Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i) is None,
            post == (Self { l2_tables: post.l2_tables, l1_rev_map: post.l1_rev_map, l1_tables: post.l1_tables, ..pre }),
            post.l1_rev_map.view() == pre.l1_rev_map.view().remove(target_l1_p),
            post.l1_tables.view() == pre.l1_tables.view().remove(target_l1_p),
            post.l2_tables.view() =~= pre.l2_tables.view().insert(target_l2_p, post.l2_tables.view().spec_index(target_l2_p)),
            post.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p,
            post.l2_tables.view().spec_index(target_l2_p).is_init(),
            post.l2_tables.view().spec_index(target_l2_p).value().wf(),
            forall|i: usize|
                #![trigger pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
                #![trigger post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
                pei_valid(i) && i != target_l2i ==> post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i) =~= pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i),
            post.l2_tables.view().spec_index(target_l2_p).value().spec_index(target_l2i) =~= (PageEntry { addr: 0, perm: PageEntryPerm {
                present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } }),
        ensures
            post.wf_mapping_4k(),
    {
        assert(post.wf_mapping_4k()) by { reveal(PageTable::wf_mapping_4k); broadcast use PageTable::resolve_l3_addr_unique_at; broadcast use PageTable::resolve_l2_addr_unique_at; };
    }

    /// EOF closure of `remove_l2_entry`: 2M and 1G abstract-mapping leaves.
    pub(super) proof fn remove_l2_entry_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).unwrap().addr == target_l1_p,
            forall|i: L1Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, i) is None,
            post == (Self { l2_tables: post.l2_tables, l1_rev_map: post.l1_rev_map, l1_tables: post.l1_tables, ..pre }),
            post.l1_rev_map.view() == pre.l1_rev_map.view().remove(target_l1_p),
            post.l1_tables.view() == pre.l1_tables.view().remove(target_l1_p),
            post.l2_tables.view() =~= pre.l2_tables.view().insert(target_l2_p, post.l2_tables.view().spec_index(target_l2_p)),
            post.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p,
            post.l2_tables.view().spec_index(target_l2_p).is_init(),
            post.l2_tables.view().spec_index(target_l2_p).value().wf(),
            forall|i: usize|
                #![trigger pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
                #![trigger post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
                pei_valid(i) && i != target_l2i ==> post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i) =~= pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i),
            post.l2_tables.view().spec_index(target_l2_p).value().spec_index(target_l2i) =~= (PageEntry { addr: 0, perm: PageEntryPerm {
                present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } }),
        ensures
            post.wf_mapping_2m(),
            post.wf_mapping_1g(),
    {
        assert(post.wf_mapping_2m()) by { reveal(PageTable::wf_mapping_2m); };
        assert(post.wf_mapping_1g()) by { reveal(PageTable::wf_mapping_1g); };
    }

    /// EOF closure of `remove_l2_entry`: walk-table reachability.
    pub(super) proof fn remove_l2_entry_eof_reachable(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, target_l1_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is Some,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).unwrap().addr == target_l1_p,
            pre.l2_tables.view().dom().contains(target_l2_p),
            pre.l1_tables.view().dom().contains(target_l1_p),
            post == (Self { l2_tables: post.l2_tables, l1_rev_map: post.l1_rev_map, l1_tables: post.l1_tables, ..pre }),
            post.l1_rev_map.view() == pre.l1_rev_map.view().remove(target_l1_p),
            post.l1_tables.view() == pre.l1_tables.view().remove(target_l1_p),
            post.l2_tables.view() =~= pre.l2_tables.view().insert(target_l2_p, post.l2_tables.view().spec_index(target_l2_p)),
            post.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p,
            post.l2_tables.view().spec_index(target_l2_p).is_init(),
            post.l2_tables.view().spec_index(target_l2_p).value().wf(),
            forall|i: usize|
                #![trigger pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
                #![trigger post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
                pei_valid(i) && i != target_l2i ==> post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i) =~= pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i),
            post.l2_tables.view().spec_index(target_l2_p).value().spec_index(target_l2i) =~= (PageEntry { addr: 0, perm: PageEntryPerm {
                present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } }),
        ensures
            post.tables_reachable_wf(),
    {
        assert(post.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); };
    }

    /// EOF closure of `remove_l3_entry`: table-structure leaves and the shrunk page closure.
    pub(super) proof fn remove_l3_entry_eof_tables(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i).unwrap().addr == target_l2_p,
            forall|i: L2Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            pre.l3_tables.view().dom().contains(target_l3_p),
            pre.l2_tables.view().dom().contains(target_l2_p),
            post == (Self { l3_tables: post.l3_tables, l2_rev_map: post.l2_rev_map, l2_tables: post.l2_tables, ..pre }),
            post.l2_rev_map.view() == pre.l2_rev_map.view().remove(target_l2_p),
            post.l2_tables.view() == pre.l2_tables.view().remove(target_l2_p),
            post.l3_tables.view() =~= pre.l3_tables.view().insert(target_l3_p, post.l3_tables.view().spec_index(target_l3_p)),
            post.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p,
            post.l3_tables.view().spec_index(target_l3_p).is_init(),
            post.l3_tables.view().spec_index(target_l3_p).value().wf(),
            forall|i: usize|
                #![trigger pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
                #![trigger post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
                pei_valid(i) && i != target_l3i ==> post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i),
            post.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i) =~= (PageEntry { addr: 0, perm: PageEntryPerm {
                present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } }),
        ensures
            post.wf_l4(),
            post.wf_l3(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l4(),
            post.disjoint_l3(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.kernel_entries_wf(),
            post.page_closure() =~= pre.page_closure().remove(target_l2_p),
    {
        assert(post.wf_l4()) by { reveal(PageTable::wf_l4); };
        assert(post.wf_l3()) by { reveal(PageTable::wf_l3); reveal(PageTable::disjoint_l3); };
        assert(post.wf_l2()) by { reveal(PageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(PageTable::wf_l1); };
        assert(post.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
        assert(post.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
        assert(post.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(PageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
        assert(post.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
        assert(post.page_closure() =~= pre.page_closure().remove(target_l2_p)) by { reveal(PageTable::table_pages_wf); };
    }

    /// EOF closure of `remove_l3_entry`: 4K abstract-mapping leaf.
    pub(super) proof fn remove_l3_entry_eof_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i).unwrap().addr == target_l2_p,
            forall|i: L2Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            post == (Self { l3_tables: post.l3_tables, l2_rev_map: post.l2_rev_map, l2_tables: post.l2_tables, ..pre }),
            post.l2_rev_map.view() == pre.l2_rev_map.view().remove(target_l2_p),
            post.l2_tables.view() == pre.l2_tables.view().remove(target_l2_p),
            post.l3_tables.view() =~= pre.l3_tables.view().insert(target_l3_p, post.l3_tables.view().spec_index(target_l3_p)),
            post.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p,
            post.l3_tables.view().spec_index(target_l3_p).is_init(),
            post.l3_tables.view().spec_index(target_l3_p).value().wf(),
            forall|i: usize|
                #![trigger pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
                #![trigger post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
                pei_valid(i) && i != target_l3i ==> post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i),
            post.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i) =~= (PageEntry { addr: 0, perm: PageEntryPerm {
                present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } }),
        ensures
            post.wf_mapping_4k(),
    {
        assert(post.wf_mapping_4k()) by { reveal(PageTable::wf_mapping_4k); reveal(PageTable::wf_l4); reveal(PageTable::disjoint_l3); };
    }

    /// EOF closure of `remove_l3_entry`: 2M and 1G abstract-mapping leaves.
    pub(super) proof fn remove_l3_entry_eof_mappings(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i).unwrap().addr == target_l2_p,
            forall|i: L2Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            post == (Self { l3_tables: post.l3_tables, l2_rev_map: post.l2_rev_map, l2_tables: post.l2_tables, ..pre }),
            post.l2_rev_map.view() == pre.l2_rev_map.view().remove(target_l2_p),
            post.l2_tables.view() == pre.l2_tables.view().remove(target_l2_p),
            post.l3_tables.view() =~= pre.l3_tables.view().insert(target_l3_p, post.l3_tables.view().spec_index(target_l3_p)),
            post.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p,
            post.l3_tables.view().spec_index(target_l3_p).is_init(),
            post.l3_tables.view().spec_index(target_l3_p).value().wf(),
            forall|i: usize|
                #![trigger pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
                #![trigger post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
                pei_valid(i) && i != target_l3i ==> post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i),
            post.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i) =~= (PageEntry { addr: 0, perm: PageEntryPerm {
                present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } }),
        ensures
            post.wf_mapping_2m(),
            post.wf_mapping_1g(),
    {
        assert(post.wf_mapping_2m()) by { reveal(PageTable::wf_mapping_2m); reveal(PageTable::wf_l4); reveal(PageTable::disjoint_l3); };
        assert(post.wf_mapping_1g()) by { reveal(PageTable::wf_mapping_1g); };
    }

    /// EOF closure of `remove_l3_entry`: walk-table reachability.
    pub(super) proof fn remove_l3_entry_eof_reachable(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, target_l2_p: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i).unwrap().addr == target_l2_p,
            forall|i: L2Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_l2(target_l4i, target_l3i, i) is None,
            forall|i: L2Index| #![auto] pei_valid(i) ==> pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, i) is None,
            post == (Self { l3_tables: post.l3_tables, l2_rev_map: post.l2_rev_map, l2_tables: post.l2_tables, ..pre }),
            post.l2_rev_map.view() == pre.l2_rev_map.view().remove(target_l2_p),
            post.l2_tables.view() == pre.l2_tables.view().remove(target_l2_p),
            post.l3_tables.view() =~= pre.l3_tables.view().insert(target_l3_p, post.l3_tables.view().spec_index(target_l3_p)),
            post.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p,
            post.l3_tables.view().spec_index(target_l3_p).is_init(),
            post.l3_tables.view().spec_index(target_l3_p).value().wf(),
            forall|i: usize|
                #![trigger pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
                #![trigger post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
                pei_valid(i) && i != target_l3i ==> post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i),
            post.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i) =~= (PageEntry { addr: 0, perm: PageEntryPerm {
                present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: false } }),
        ensures
            post.tables_reachable_wf(),
    {
        assert(post.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); reveal(PageTable::wf_l4); reveal(PageTable::disjoint_l4); broadcast use PageTable::resolve_l3_addr_unique_at; };
    }
}
} // verus!
