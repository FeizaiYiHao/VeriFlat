use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> PageTableC<TABLE_TYPE> {
    /// Operation-state summary of `create_entry_l4`: root entry `target_l4i` now links the new empty L3 page `page_map_ptr`, which
    /// joins the L3 pages with reverse index `target_l4i`; the window half and every other field are unchanged.
    #[verifier::opaque]
    pub open spec fn create_entry_l4_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr) -> bool {
        &&& post.lower == pre.lower
        &&& post.higher == (PageTableHigher { l4_table: post.higher.l4_table, l3_rev_map: post.higher.l3_rev_map, l3_tables: post.higher.l3_tables, ..pre.higher })
        &&& post.higher.l4_table.view().dom() == pre.higher.l4_table.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.higher.l4_table.view().spec_index(p)]
            pre.higher.l4_table.view().dom().contains(p) && p != pre.higher.cr3 ==> post.higher.l4_table.view().spec_index(p) == pre.higher.l4_table.view().spec_index(p)
        &&& post.higher.l4_table.view().spec_index(pre.higher.cr3).addr() == pre.higher.cr3
        &&& post.higher.l4_table.view().spec_index(pre.higher.cr3).is_init()
        &&& post.higher.l4_table.view().spec_index(pre.higher.cr3).value().wf()
        &&& forall|i: usize| #![trigger post.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(i)]
            pei_valid(i) && i != target_l4i ==> post.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(i) =~= pre.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(i)
        &&& post.higher.l4_table.view().spec_index(pre.higher.cr3).value().spec_index(target_l4i) =~= (PageEntry {
            addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: false } })
        &&& post.higher.l3_tables.view() == pre.higher.l3_tables.view().insert(page_map_ptr, post.higher.l3_tables.view().spec_index(page_map_ptr))
        &&& post.higher.l3_tables.view().spec_index(page_map_ptr).addr() == page_map_ptr
        &&& post.higher.l3_tables.view().spec_index(page_map_ptr).is_init()
        &&& post.higher.l3_tables.view().spec_index(page_map_ptr).value().wf()
        &&& forall|i: usize| #![trigger post.higher.l3_tables.view().spec_index(page_map_ptr).value().spec_index(i)]
            pei_valid(i) ==> post.higher.l3_tables.view().spec_index(page_map_ptr).value().spec_index(i).is_empty()
        &&& post.higher.l3_rev_map.view() == pre.higher.l3_rev_map.view().insert(page_map_ptr, target_l4i)
    }

    /// EOF closure of `create_entry_l4`: every page-table invariant leaf.
    pub(super) proof fn create_entry_l4_eof(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf(),
    {
        Self::create_entry_l4_eof_higher_inv(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_table_leaves(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_mapping_4k(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_mapping_2m(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_tables_reachable_wf(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_wf_window_locks(pre, post, target_l4i, page_map_ptr);
    }

    /// EOF closure of `create_entry_l4`: the big-lock invariant.
    proof fn create_entry_l4_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.higher.inv(),
    {
        reveal(PageTableC::create_entry_l4_eof_transition_framing);
        assert(post.higher.wf_l4()) by { reveal(PageTableHigher::wf_l4); };
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); reveal(PageTableHigher::wf_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); reveal(PageTableHigher::wf_l4); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `create_entry_l4`: the table-shape leaves of the window half.
    proof fn create_entry_l4_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_l3(),
            post.l2_tokens_paired(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.va_addr_valid(),
    {
        reveal(PageTableC::create_entry_l4_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
        assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
        assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
        assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
        assert(post.user_only()) by { reveal(PageTableC::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
    }

    /// EOF closure of `create_entry_l4`: `wf_mapping_4k`.
    proof fn create_entry_l4_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(PageTableC::create_entry_l4_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); reveal(PageTableHigher::wf_l4); };
    }

    /// EOF closure of `create_entry_l4`: `wf_mapping_2m`.
    proof fn create_entry_l4_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(PageTableC::create_entry_l4_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); reveal(PageTableHigher::wf_l4); };
    }

    /// EOF closure of `create_entry_l4`: `tables_reachable_wf`.
    proof fn create_entry_l4_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(PageTableC::create_entry_l4_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); reveal(PageTableHigher::wf_l4); };
    }

    /// EOF closure of `create_entry_l4`: `wf_window_locks`.
    proof fn create_entry_l4_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_resolve_mapping_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_window_locks(),
    {
        reveal(PageTableC::create_entry_l4_eof_transition_framing);
        assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); reveal(PageTableHigher::wf_l4); broadcast use spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip; };
    }

    /// Operation-state summary of `create_entry_l3`: L3 entry `target_l3i` of `target_l3_p` now links the new empty, unlocked L2 page
    /// `page_map_ptr`, which joins the L2 pages with its three tokens and reverse index `(target_l4i, target_l3i)`; every other
    /// field is unchanged.
    #[verifier::opaque]
    pub open spec fn create_entry_l3_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr) -> bool {
        &&& post.higher == (PageTableHigher { l3_tables: post.higher.l3_tables, l2_rev_map: post.higher.l2_rev_map, ..pre.higher })
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, l2_ghost: post.lower.l2_ghost, l2_lock: post.lower.l2_lock, ..pre.lower })
        &&& post.higher.l3_tables.view().dom() == pre.higher.l3_tables.view().dom()
        &&& forall|p: PageMapPtr| #![trigger post.higher.l3_tables.view().spec_index(p)]
            pre.higher.l3_tables.view().dom().contains(p) && p != target_l3_p ==> post.higher.l3_tables.view().spec_index(p) == pre.higher.l3_tables.view().spec_index(p)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).addr() == target_l3_p
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).is_init()
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().wf()
        &&& forall|i: usize| #![trigger post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)]
            pei_valid(i) && i != target_l3i ==> post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i) =~= pre.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(i)
        &&& post.higher.l3_tables.view().spec_index(target_l3_p).value().spec_index(target_l3i) =~= (PageEntry {
            addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } })
        &&& post.higher.l2_rev_map.view() == pre.higher.l2_rev_map.view().insert(page_map_ptr, (target_l4i, target_l3i))
        &&& post.lower.l2_perms == pre.lower.l2_perms.insert(page_map_ptr, post.lower.l2_perms.spec_index(page_map_ptr))
        &&& post.lower.l2_perms.spec_index(page_map_ptr).addr() == page_map_ptr
        &&& post.lower.l2_perms.spec_index(page_map_ptr).is_init()
        &&& post.lower.l2_perms.spec_index(page_map_ptr).value().addr() == page_map_ptr
        &&& post.lower.l2_ghost == pre.lower.l2_ghost.insert(page_map_ptr, post.lower.l2_page(page_map_ptr))
        &&& post.lower.l2_page(page_map_ptr).addr() == page_map_ptr
        &&& post.lower.l2_page(page_map_ptr).wf()
        &&& forall|i: usize|
            #![trigger post.lower.l2_page(page_map_ptr).spec_index(i).is_empty()]
            #![trigger post.lower.l2_page(page_map_ptr).spec_index(i).perm.present]
            #![trigger post.lower.l2_page(page_map_ptr).spec_index(i).perm.ps]
            #![trigger post.lower.l2_page(page_map_ptr).spec_index(i).perm.kernel_present]
            pei_valid(i) ==> post.lower.l2_page(page_map_ptr).spec_index(i).is_empty()
        &&& post.lower.l2_lock == pre.lower.l2_lock.insert(page_map_ptr, post.lower.l2_lock_of(page_map_ptr))
        &&& post.lower.l2_lock_of(page_map_ptr).addr() == page_map_ptr
        &&& post.lower.l2_lock_of(page_map_ptr).wf()
        &&& forall|i: usize| #![trigger post.lower.l2_lock_of(page_map_ptr).lock_state(i)] pei_valid(i) ==> post.lower.l2_lock_of(page_map_ptr).lock_state(i) is None
    }

    /// EOF closure of `create_entry_l3`: every page-table invariant leaf.
    pub(super) proof fn create_entry_l3_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
        Self::create_entry_l3_eof_higher_inv(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
        Self::create_entry_l3_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr);
    }

    /// EOF closure of `create_entry_l3`: the big-lock invariant.
    proof fn create_entry_l3_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.higher.inv(),
    {
        reveal(PageTableC::create_entry_l3_eof_transition_framing);
        assert(post.higher.wf_l4()) by { reveal(PageTableHigher::wf_l4); };
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); reveal(PageTableC::wf_l3); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); reveal(PageTableHigher::wf_l4); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `create_entry_l3`: the table-shape leaves of the window half.
    proof fn create_entry_l3_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
            post.l2_tokens_paired(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.va_addr_valid(),
    {
        reveal(PageTableC::create_entry_l3_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
        assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
        assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
        assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
        assert(post.user_only()) by { reveal(PageTableC::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
    }

    /// EOF closure of `create_entry_l3`: `wf_mapping_4k`.
    proof fn create_entry_l3_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
        reveal(PageTableC::create_entry_l3_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); reveal(PageTableHigher::wf_l4); reveal(PageTableC::wf_l3); };
    }

    /// EOF closure of `create_entry_l3`: `wf_mapping_2m`.
    proof fn create_entry_l3_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
        reveal(PageTableC::create_entry_l3_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); reveal(PageTableHigher::wf_l4); reveal(PageTableC::wf_l3); };
    }

    /// EOF closure of `create_entry_l3`: `tables_reachable_wf`.
    proof fn create_entry_l3_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
        reveal(PageTableC::create_entry_l3_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); reveal(PageTableHigher::wf_l4); reveal(PageTableC::wf_l3); reveal(PageTableHigher::disjoint_l4); };
    }

    /// EOF closure of `create_entry_l3`: `wf_window_locks`.
    proof fn create_entry_l3_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr),
        ensures
            post.wf_window_locks(),
    {
        reveal(PageTableC::create_entry_l3_eof_transition_framing);
        assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); reveal(PageTableHigher::wf_l4); reveal(PageTableC::wf_l3); broadcast use spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip; };
    }

    /// Operation-state summary of `create_entry_l2`: entry `target_l2i` of L2 page `target_l2_p` now links the new empty L1 page
    /// `page_map_ptr`, which joins the L1 pages with reverse index `(target_l4i, target_l3i, target_l2i)`; the big-lock payload, the
    /// window locks, and every other field are unchanged.
    #[verifier::opaque]
    pub open spec fn create_entry_l2_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_ghost: post.lower.l2_ghost, l1_rev_map: post.lower.l1_rev_map, l1_tables: post.lower.l1_tables, ..pre.lower })
        &&& post.lower.l2_ghost.dom() == pre.lower.l2_ghost.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_page(p)] pre.lower.l2_ghost.dom().contains(p) && p != target_l2_p ==> post.lower.l2_page(p) == pre.lower.l2_page(p)
        &&& post.lower.l2_page(target_l2_p).addr() == target_l2_p
        &&& post.lower.l2_page(target_l2_p).wf()
        &&& forall|i: usize| #![trigger post.lower.l2_page(target_l2_p).spec_index(i)]
            pei_valid(i) && i != target_l2i ==> post.lower.l2_page(target_l2_p).spec_index(i) =~= pre.lower.l2_page(target_l2_p).spec_index(i)
        &&& post.lower.l2_page(target_l2_p).spec_index(target_l2i) =~= (PageEntry {
            addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } })
        &&& post.lower.l1_tables == pre.lower.l1_tables.insert(page_map_ptr, post.lower.l1_tables.spec_index(page_map_ptr))
        &&& post.lower.l1_tables.spec_index(page_map_ptr).addr() == page_map_ptr
        &&& post.lower.l1_tables.spec_index(page_map_ptr).is_init()
        &&& post.lower.l1_tables.spec_index(page_map_ptr).value().wf()
        &&& forall|i: usize|
            #![trigger post.lower.l1_tables.spec_index(page_map_ptr).value().spec_index(i).is_empty()]
            #![trigger post.lower.l1_tables.spec_index(page_map_ptr).value().spec_index(i).perm.present]
            #![trigger post.lower.l1_tables.spec_index(page_map_ptr).value().spec_index(i).perm.ps]
            #![trigger post.lower.l1_tables.spec_index(page_map_ptr).value().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> post.lower.l1_tables.spec_index(page_map_ptr).value().spec_index(i).is_empty()
        &&& post.lower.l1_rev_map == pre.lower.l1_rev_map.insert(page_map_ptr, (target_l4i, target_l3i, target_l2i))
    }

    /// EOF closure of `create_entry_l2`: every page-table invariant leaf.
    pub(super) proof fn create_entry_l2_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
        Self::create_entry_l2_eof_higher_inv(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
    }

    /// EOF closure of `create_entry_l2`: the big-lock invariant.
    proof fn create_entry_l2_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
            post.higher.inv(),
    {
        reveal(PageTableC::create_entry_l2_eof_transition_framing);
    }

    /// EOF closure of `create_entry_l2`: the table-shape leaves of the window half.
    proof fn create_entry_l2_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
            post.l2_tokens_paired(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.va_addr_valid(),
    {
        reveal(PageTableC::create_entry_l2_eof_transition_framing);
        assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
        assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
        assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); reveal(PageTableC::l2_tokens_paired); };
        assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); reveal(PageTableC::wf_l2); reveal(PageTableC::l2_tokens_paired); };
        assert(post.user_only()) by { reveal(PageTableC::user_only); reveal(PageTableC::l2_tokens_paired); };
        assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); reveal(PageTableC::l2_tokens_paired); };
        assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
    }

    /// EOF closure of `create_entry_l2`: `wf_mapping_4k`.
    proof fn create_entry_l2_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
        reveal(PageTableC::create_entry_l2_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); reveal(PageTableHigher::wf_l4); reveal(PageTableC::wf_l3); reveal(PageTableC::wf_l2); reveal(PageTableC::l2_tokens_paired); };
    }

    /// EOF closure of `create_entry_l2`: `wf_mapping_2m`.
    proof fn create_entry_l2_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
        reveal(PageTableC::create_entry_l2_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); reveal(PageTableHigher::wf_l4); reveal(PageTableC::wf_l3); reveal(PageTableC::l2_tokens_paired); };
    }

    /// EOF closure of `create_entry_l2`: `tables_reachable_wf`.
    proof fn create_entry_l2_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
        reveal(PageTableC::create_entry_l2_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); reveal(PageTableHigher::wf_l4); reveal(PageTableC::wf_l3); reveal(PageTableC::wf_l2); reveal(PageTableC::l2_tokens_paired); broadcast use PageTableHigher::resolve_l3_addr_unique_at; };
    }

    /// EOF closure of `create_entry_l2`: `wf_window_locks`.
    proof fn create_entry_l2_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
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
            post.wf_window_locks(),
    {
        reveal(PageTableC::create_entry_l2_eof_transition_framing);
        assert(post.wf_window_locks()) by { reveal(PageTableC::wf_window_locks); };
    }
}
} // verus!
