use vstd::prelude::*;
verus! {
use crate::*;
use super::pagetable_spec::*;
use super::entry::*;

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    /// Operation-state summary of `create_entry_l4`: the root map's entry `target_l4i` now points to the new empty L3 map
    /// `page_map_ptr`, which joins the L3 maps with reverse index `target_l4i`; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn create_entry_l4_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr) -> bool {
        &&& post == (Self { l4_table: post.l4_table, l3_rev_map: post.l3_rev_map, l3_tables: post.l3_tables, ..pre })
        &&& post.l4_table.view().dom() == pre.l4_table.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.l4_table.view().spec_index(p)] pre.l4_table.view().dom().contains(p) && p != pre.cr3 ==> post.l4_table.view().spec_index(p) == pre.l4_table.view().spec_index(p)
        &&& post.l4_table.view().spec_index(pre.cr3).addr() == pre.cr3
        &&& post.l4_table.view().spec_index(pre.cr3).is_init()
        &&& post.l4_table.view().spec_index(pre.cr3).value().wf()
        &&& forall|i: usize| #![trigger post.l4_table.view().spec_index(pre.cr3).value().spec_index(i)]
            pei_valid(i) && i != target_l4i ==> post.l4_table.view().spec_index(pre.cr3).value().spec_index(i) =~= pre.l4_table.view().spec_index(pre.cr3).value().spec_index(i)
        &&& post.l4_table.view().spec_index(pre.cr3).value().spec_index(target_l4i) =~= (PageEntry {
            addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: false } })
        &&& post.l3_tables.view() == pre.l3_tables.view().insert(page_map_ptr, post.l3_tables.view().spec_index(page_map_ptr))
        &&& post.l3_tables.view().spec_index(page_map_ptr).addr() == page_map_ptr
        &&& post.l3_tables.view().spec_index(page_map_ptr).is_init()
        &&& post.l3_tables.view().spec_index(page_map_ptr).value().wf()
        &&& forall|i: usize| #![trigger post.l3_tables.view().spec_index(page_map_ptr).value().spec_index(i)] pei_valid(i) ==> post.l3_tables.view().spec_index(page_map_ptr).value().spec_index(i).is_empty()
        &&& post.l3_rev_map.view() == pre.l3_rev_map.view().insert(page_map_ptr, target_l4i)
    }

    /// EOF closure of `create_entry_l4`: every page-table invariant leaf.
    pub(super) proof fn create_entry_l4_eof(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf(),
    {
        Self::create_entry_l4_eof_wf_l4(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_l3(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_l2(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_l1(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_disjoint_l4(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_disjoint_l3(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_disjoint_l2(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_mapping_4k(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_mapping_2m(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_mapping_1g(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_user_only(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_rwx_upper_level_entries(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_table_pages_wf(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_tables_reachable_wf(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_kernel_entries_wf(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_va_addr_valid_and_pcid_wf(pre, post, target_l4i, page_map_ptr);
    }

    /// EOF closure of `create_entry_l4`: `wf_l4`.
    proof fn create_entry_l4_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_l4(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(PageTable::wf_l4); };
    }

    /// EOF closure of `create_entry_l4`: `wf_l3`.
    proof fn create_entry_l4_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_l3(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTable::wf_l3); };
    }

    /// EOF closure of `create_entry_l4`: `wf_l2`.
    proof fn create_entry_l4_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_l2(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(PageTable::wf_l2); };
    }

    /// EOF closure of `create_entry_l4`: `wf_l1`.
    proof fn create_entry_l4_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_l1(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(PageTable::wf_l1); };
    }

    /// EOF closure of `create_entry_l4`: `disjoint_l4`.
    proof fn create_entry_l4_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.disjoint_l4(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(PageTable::disjoint_l4); reveal(PageTable::wf_l4); };
    }

    /// EOF closure of `create_entry_l4`: `disjoint_l3`.
    proof fn create_entry_l4_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.disjoint_l3(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
    }

    /// EOF closure of `create_entry_l4`: `disjoint_l2`.
    proof fn create_entry_l4_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.disjoint_l2(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
    }

    /// EOF closure of `create_entry_l4`: `wf_mapping_4k`.
    proof fn create_entry_l4_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_mapping_4k()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)] #![trigger pre.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)) by { reveal(PageTable::wf_l4); };
            reveal(PageTable::wf_mapping_4k);
        };
    }

    /// EOF closure of `create_entry_l4`: `wf_mapping_2m`.
    proof fn create_entry_l4_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_mapping_2m()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)] #![trigger pre.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == post.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)) by { reveal(PageTable::wf_l4); };
            reveal(PageTable::wf_mapping_2m);
        };
    }

    /// EOF closure of `create_entry_l4`: `wf_mapping_1g`.
    proof fn create_entry_l4_eof_wf_mapping_1g(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_mapping_1g(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_mapping_1g()) by {
            assert(forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i,l3i)] #![trigger pre.spec_resolve_mapping_1g_l3(l4i,l3i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i)
                ==> pre.spec_resolve_mapping_1g_l3(l4i, l3i) == post.spec_resolve_mapping_1g_l3(l4i, l3i)) by { reveal(PageTable::wf_l4); };
            reveal(PageTable::wf_mapping_1g);
        };
    }

    /// EOF closure of `create_entry_l4`: `user_only`.
    proof fn create_entry_l4_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.user_only(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.user_only()) by { reveal(PageTable::user_only); };
    }

    /// EOF closure of `create_entry_l4`: `rwx_upper_level_entries`.
    proof fn create_entry_l4_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `create_entry_l4`: `table_pages_wf`.
    proof fn create_entry_l4_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.table_pages_wf(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
    }

    /// EOF closure of `create_entry_l4`: `tables_reachable_wf`.
    proof fn create_entry_l4_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); reveal(PageTable::wf_l4); };
    }

    /// EOF closure of `create_entry_l4`: `kernel_entries_wf`.
    proof fn create_entry_l4_eof_kernel_entries_wf(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.kernel_entries_wf(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
        assert(post.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
    }

    /// EOF closure of `create_entry_l4`: `va_addr_valid` and `pcid_wf`.
    proof fn create_entry_l4_eof_va_addr_valid_and_pcid_wf(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.va_addr_valid(),
            post.pcid_wf(),
    {
        reveal(PageTable::create_entry_l4_eof_transition_framing);
    }

    /// Operation-state summary of `create_entry_l3`: the L3 map `target_l3_p` now has entry `target_l3i` pointing to the new empty L2 map
    /// `page_map_ptr`, which joins the L2 maps with reverse index `(target_l4i, target_l3i)`; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn create_entry_l3_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr) -> bool {
        &&& post == (Self { l3_tables: post.l3_tables, l2_rev_map: post.l2_rev_map, l2_tables: post.l2_tables, ..pre })
        &&& post.l3_tables.view().dom() == pre.l3_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.l3_tables.view().spec_index(p)] pre.l3_tables.view().dom().contains(p) && p != target_l3_p ==> post.l3_tables.view().spec_index(p) == pre.l3_tables.view().spec_index(p)
        &&& post.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
        &&& post.l3_tables.view().spec_index(target_l3_p).is_init()
        &&& post.l3_tables.view().spec_index(target_l3_p).value().wf()
        &&& forall|i: usize| #![trigger post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
            pei_valid(i) && i != target_l3i ==> post.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)
        &&& post.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i) =~= (PageEntry {
            addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } })
        &&& post.l2_tables.view() == pre.l2_tables.view().insert(page_map_ptr, post.l2_tables.view().spec_index(page_map_ptr))
        &&& post.l2_tables.view().spec_index(page_map_ptr).addr() == page_map_ptr
        &&& post.l2_tables.view().spec_index(page_map_ptr).is_init()
        &&& post.l2_tables.view().spec_index(page_map_ptr).value().wf()
        &&& forall|i: usize| #![trigger post.l2_tables.view().spec_index(page_map_ptr).value().spec_index(i).is_empty()] #![trigger post.l2_tables.view().spec_index(page_map_ptr).value().spec_index(i).perm.present]
            #![trigger post.l2_tables.view().spec_index(page_map_ptr).value().spec_index(i).perm.ps] #![trigger post.l2_tables.view().spec_index(page_map_ptr).value().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> post.l2_tables.view().spec_index(page_map_ptr).value().spec_index(i).is_empty()
        &&& post.l2_rev_map.view() == pre.l2_rev_map.view().insert(page_map_ptr, (target_l4i, target_l3i))
    }

    /// EOF closure of `create_entry_l3`: every page-table invariant leaf.
    pub(super) proof fn create_entry_l3_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf(),
    {
        Self::create_entry_l3_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_disjoint_l4(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_disjoint_l3(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_mapping_1g(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_user_only(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_kernel_entries_wf(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_va_addr_valid_and_pcid_wf(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
    }

    /// EOF closure of `create_entry_l3`: `wf_l4`.
    proof fn create_entry_l3_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf_l4(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(PageTable::wf_l4); };
    }

    /// EOF closure of `create_entry_l3`: `wf_l3`.
    proof fn create_entry_l3_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf_l3(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTable::wf_l3); };
    }

    /// EOF closure of `create_entry_l3`: `wf_l2`.
    proof fn create_entry_l3_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf_l2(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(PageTable::wf_l2); };
    }

    /// EOF closure of `create_entry_l3`: `wf_l1`.
    proof fn create_entry_l3_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf_l1(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(PageTable::wf_l1); };
    }

    /// EOF closure of `create_entry_l3`: `disjoint_l4`.
    proof fn create_entry_l3_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.disjoint_l4(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `create_entry_l3`: `disjoint_l3`.
    proof fn create_entry_l3_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.disjoint_l3(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(PageTable::disjoint_l3); reveal(PageTable::wf_l3); };
    }

    /// EOF closure of `create_entry_l3`: `disjoint_l2`.
    proof fn create_entry_l3_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.disjoint_l2(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(PageTable::disjoint_l2); };
    }

    /// EOF closure of `create_entry_l3`: `wf_mapping_4k`.
    proof fn create_entry_l3_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_mapping_4k()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)] #![trigger pre.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)) by { reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); };
            reveal(PageTable::wf_mapping_4k);
        };
    }

    /// EOF closure of `create_entry_l3`: `wf_mapping_2m`.
    proof fn create_entry_l3_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_mapping_2m()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)] #![trigger pre.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == post.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)) by { reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); };
            reveal(PageTable::wf_mapping_2m);
        };
    }

    /// EOF closure of `create_entry_l3`: `wf_mapping_1g`.
    proof fn create_entry_l3_eof_wf_mapping_1g(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf_mapping_1g(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_mapping_1g()) by {
            assert(forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_resolve_mapping_1g_l3(l4i,l3i)] #![trigger pre.spec_resolve_mapping_1g_l3(l4i,l3i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i,target_l3i)
                ==> pre.spec_resolve_mapping_1g_l3(l4i, l3i) =~= post.spec_resolve_mapping_1g_l3(l4i, l3i)) by { reveal(PageTable::wf_l4); };
            reveal(PageTable::wf_mapping_1g);
        };
    }

    /// EOF closure of `create_entry_l3`: `user_only`.
    proof fn create_entry_l3_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.user_only(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.user_only()) by { reveal(PageTable::user_only); };
    }

    /// EOF closure of `create_entry_l3`: `rwx_upper_level_entries`.
    proof fn create_entry_l3_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `create_entry_l3`: `table_pages_wf`.
    proof fn create_entry_l3_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.table_pages_wf(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
    }

    /// EOF closure of `create_entry_l3`: `tables_reachable_wf`.
    proof fn create_entry_l3_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `create_entry_l3`: `kernel_entries_wf`.
    proof fn create_entry_l3_eof_kernel_entries_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.kernel_entries_wf(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
        assert(post.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
    }

    /// EOF closure of `create_entry_l3`: `va_addr_valid` and `pcid_wf`.
    proof fn create_entry_l3_eof_va_addr_valid_and_pcid_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.va_addr_valid(),
            post.pcid_wf(),
    {
        reveal(PageTable::create_entry_l3_eof_transition_framing);
    }

    /// Operation-state summary of `create_entry_l2`: the L2 map `target_l2_p` now has entry `target_l2i` pointing to the new empty L1 map
    /// `page_map_ptr`, which joins the L1 maps with reverse index `(target_l4i, target_l3i, target_l2i)`; every other field is unchanged.
    #[verifier::opaque]
    pub open spec fn create_entry_l2_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr) -> bool {
        &&& post == (Self { l2_tables: post.l2_tables, l1_rev_map: post.l1_rev_map, l1_tables: post.l1_tables, ..pre })
        &&& post.l2_tables.view().dom() == pre.l2_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.l2_tables.view().spec_index(p)] pre.l2_tables.view().dom().contains(p) && p != target_l2_p ==> post.l2_tables.view().spec_index(p) == pre.l2_tables.view().spec_index(p)
        &&& post.l2_tables.view().spec_index(target_l2_p).addr() == target_l2_p
        &&& post.l2_tables.view().spec_index(target_l2_p).is_init()
        &&& post.l2_tables.view().spec_index(target_l2_p).value().wf()
        &&& forall|i: usize| #![trigger post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)]
            pei_valid(i) && i != target_l2i ==> post.l2_tables.view().spec_index(target_l2_p).value().spec_index(i) =~= pre.l2_tables.view().spec_index(target_l2_p).value().spec_index(i)
        &&& post.l2_tables.view().spec_index(target_l2_p).value().spec_index(target_l2i) =~= (PageEntry {
            addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } })
        &&& post.l1_tables.view() == pre.l1_tables.view().insert(page_map_ptr, post.l1_tables.view().spec_index(page_map_ptr))
        &&& post.l1_tables.view().spec_index(page_map_ptr).addr() == page_map_ptr
        &&& post.l1_tables.view().spec_index(page_map_ptr).is_init()
        &&& post.l1_tables.view().spec_index(page_map_ptr).value().wf()
        &&& forall|i: usize| #![trigger post.l1_tables.view().spec_index(page_map_ptr).value().spec_index(i).is_empty()] #![trigger post.l1_tables.view().spec_index(page_map_ptr).value().spec_index(i).perm.present]
            #![trigger post.l1_tables.view().spec_index(page_map_ptr).value().spec_index(i).perm.ps] #![trigger post.l1_tables.view().spec_index(page_map_ptr).value().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> post.l1_tables.view().spec_index(page_map_ptr).value().spec_index(i).is_empty()
        &&& post.l1_rev_map.view() == pre.l1_rev_map.view().insert(page_map_ptr, (target_l4i, target_l3i, target_l2i))
    }

    /// EOF closure of `create_entry_l2`: every page-table invariant leaf.
    pub(super) proof fn create_entry_l2_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf(),
    {
        Self::create_entry_l2_eof_wf_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_l1(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_disjoint_l4(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_disjoint_l3(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_disjoint_l2(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_mapping_1g(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_user_only(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_rwx_upper_level_entries(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_table_pages_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_kernel_entries_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_va_addr_valid_and_pcid_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
    }

    /// EOF closure of `create_entry_l2`: `wf_l4`.
    proof fn create_entry_l2_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf_l4(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_l4()) by { reveal(PageTable::wf_l4); };
    }

    /// EOF closure of `create_entry_l2`: `wf_l3`.
    proof fn create_entry_l2_eof_wf_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf_l3(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTable::wf_l3); };
    }

    /// EOF closure of `create_entry_l2`: `wf_l2`.
    proof fn create_entry_l2_eof_wf_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf_l2(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_l2()) by { reveal(PageTable::wf_l2); };
    }

    /// EOF closure of `create_entry_l2`: `wf_l1`.
    proof fn create_entry_l2_eof_wf_l1(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf_l1(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_l1()) by { reveal(PageTable::wf_l1); };
    }

    /// EOF closure of `create_entry_l2`: `disjoint_l4`.
    proof fn create_entry_l2_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.disjoint_l4(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.disjoint_l4()) by { reveal(PageTable::disjoint_l4); };
    }

    /// EOF closure of `create_entry_l2`: `disjoint_l3`.
    proof fn create_entry_l2_eof_disjoint_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.disjoint_l3(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.disjoint_l3()) by { reveal(PageTable::disjoint_l3); };
    }

    /// EOF closure of `create_entry_l2`: `disjoint_l2`.
    proof fn create_entry_l2_eof_disjoint_l2(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.disjoint_l2(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.disjoint_l2()) by { reveal(PageTable::disjoint_l2); reveal(PageTable::wf_l2); };
    }

    /// EOF closure of `create_entry_l2`: `wf_mapping_4k`.
    proof fn create_entry_l2_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_mapping_4k()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index| #![trigger post.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)] #![trigger pre.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
                ==> pre.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i) == post.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i)) by { reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); reveal(PageTable::wf_l2); };
            reveal(PageTable::wf_mapping_4k);
        };
    }

    /// EOF closure of `create_entry_l2`: `wf_mapping_2m`.
    proof fn create_entry_l2_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_mapping_2m()) by {
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)] #![trigger pre.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                post.kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                ==> pre.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == post.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)) by { reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); };
            reveal(PageTable::wf_mapping_2m);
        };
    }

    /// EOF closure of `create_entry_l2`: `wf_mapping_1g`.
    proof fn create_entry_l2_eof_wf_mapping_1g(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf_mapping_1g(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_mapping_1g()) by { reveal(PageTable::wf_mapping_1g); };
    }

    /// EOF closure of `create_entry_l2`: `user_only`.
    proof fn create_entry_l2_eof_user_only(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.user_only(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.user_only()) by { reveal(PageTable::user_only); };
    }

    /// EOF closure of `create_entry_l2`: `rwx_upper_level_entries`.
    proof fn create_entry_l2_eof_rwx_upper_level_entries(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.rwx_upper_level_entries(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.rwx_upper_level_entries()) by { reveal(PageTable::rwx_upper_level_entries); };
    }

    /// EOF closure of `create_entry_l2`: `table_pages_wf`.
    proof fn create_entry_l2_eof_table_pages_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.table_pages_wf(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.table_pages_wf()) by { reveal(PageTable::table_pages_wf); };
    }

    /// EOF closure of `create_entry_l2`: `tables_reachable_wf`.
    proof fn create_entry_l2_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTable::tables_reachable_wf); reveal(PageTable::wf_l4); reveal(PageTable::wf_l3); reveal(PageTable::wf_l2); broadcast use PageTable::resolve_l3_addr_unique_at; };
    }

    /// EOF closure of `create_entry_l2`: `kernel_entries_wf`.
    proof fn create_entry_l2_eof_kernel_entries_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.kernel_entries_wf(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
        assert(post.kernel_entries_wf()) by { reveal(PageTable::kernel_entries_wf); };
    }

    /// EOF closure of `create_entry_l2`: `va_addr_valid` and `pcid_wf`.
    proof fn create_entry_l2_eof_va_addr_valid_and_pcid_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.va_addr_valid(),
            post.pcid_wf(),
    {
        reveal(PageTable::create_entry_l2_eof_transition_framing);
    }
}
} // verus!
