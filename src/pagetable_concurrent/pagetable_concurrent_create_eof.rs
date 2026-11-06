use vstd::prelude::*;
verus! {
use crate::*;

impl<const TABLE_TYPE: PTType> WholePageTable<TABLE_TYPE> {
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
            pre.spec_held_l4(target_l4i) is None,
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
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.higher.inv(),
    {
        Self::create_entry_l4_eof_wf_l4(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_disjoint_l4(pre, post, target_l4i, page_map_ptr);
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); reveal(PageTableHigher::wf_l4); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `create_entry_l4`: `wf_l4`.
    proof fn create_entry_l4_eof_wf_l4(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.higher.wf_l4(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.higher.wf_l4(),
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `create_entry_l4`: `disjoint_l4`; the new L3 page lies outside the old closure.
    proof fn create_entry_l4_eof_disjoint_l4(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.higher.disjoint_l4(),
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        assert(!pre.higher.l3_tables.view().dom().contains(page_map_ptr));
        reveal(PageTableHigher::disjoint_l4);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `create_entry_l4`: the table-shape leaves of the window half.
    proof fn create_entry_l4_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.va_addr_valid(),
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `create_entry_l4`: `wf_mapping_4k`.
    proof fn create_entry_l4_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); reveal(PageTableHigher::wf_l4); };
    }

    /// EOF closure of `create_entry_l4`: `wf_mapping_2m`.
    proof fn create_entry_l4_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); reveal(PageTableHigher::wf_l4); };
    }

    /// EOF closure of `create_entry_l4`: `tables_reachable_wf`.
    proof fn create_entry_l4_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.tables_reachable_wf(),
    {
        Self::create_entry_l4_eof_tables_reachable_l2_pages(pre, post, target_l4i, page_map_ptr);
        Self::create_entry_l4_eof_tables_reachable_l1_pages(pre, post, target_l4i, page_map_ptr);
        reveal(WholePageTable::tables_reachable_wf);
    }

    /// EOF closure of `create_entry_l4`: the L2-page half of `tables_reachable_wf`.
    proof fn create_entry_l4_eof_tables_reachable_l2_pages(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            forall|p: PageMapPtr|
                #![trigger post.lower.l2_perms.dom().contains(p)]
                post.lower.l2_perms.dom().contains(p) ==> {
                    let (l4i, l3i) = post.higher.l2_rev_map.view().spec_index(p);
                    &&& post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
                    &&& post.spec_held_l3(l4i, l3i) is Some && post.spec_held_l3(l4i, l3i)->0.addr == p
                },
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        reveal(WholePageTable::tables_reachable_wf);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `create_entry_l4`: the L1-page half of `tables_reachable_wf`.
    proof fn create_entry_l4_eof_tables_reachable_l1_pages(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            forall|p: PageMapPtr|
                #![trigger post.lower.l1_rev_map.dom().contains(p)]
                post.lower.l1_rev_map.dom().contains(p) ==> {
                    let (l4i, l3i, l2i) = post.lower.l1_rev_map.spec_index(p);
                    &&& post.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    &&& post.spec_held_l3(l4i, l3i) is Some
                    &&& post.lower.l2_page(post.spec_held_l3(l4i, l3i)->0.addr).entry_lock(l2i).l1() is Some
                    &&& post.lower.l2_entry(post.spec_held_l3(l4i, l3i)->0.addr, l2i).addr == p
                },
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        reveal(WholePageTable::tables_reachable_wf);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `create_entry_l4`: `wf_window_locks`.
    proof fn create_entry_l4_eof_wf_window_locks(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            post.wf_window_locks(),
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::tables_reachable_wf); broadcast use spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip; };
    }

    /// Operation-state summary of `create_entry_l3`: L3 entry `target_l3i` of `target_l3_p` now links the new empty L2 page
    /// `page_map_ptr`, which joins the L2 pages with reverse index `(target_l4i, target_l3i)` and adds its windows to the window lock map; every other
    /// field is unchanged.
    #[verifier::opaque]
    pub open spec fn create_entry_l3_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId) -> bool {
        &&& post.higher == (PageTableHigher { l3_tables: post.higher.l3_tables, l2_rev_map: post.higher.l2_rev_map, ..pre.higher })
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, pagetable_window_locks: post.lower.pagetable_window_locks, ..pre.lower })
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
        &&& post.lower.l2_page(page_map_ptr).addr() == page_map_ptr
        &&& post.lower.l2_page(page_map_ptr).wf()
        &&& forall|i: L2Index| #![trigger post.lower.l2_page(page_map_ptr).entry_lock(i)]
            pei_valid(i) ==> post.lower.l2_entry(page_map_ptr, i).is_empty() && post.lower.l2_page(page_map_ptr).entry_lock(i).l1() is None
        &&& forall|i: L2Index| #![trigger post.lower.l2_owner(page_map_ptr, i)] pei_valid(i) && !(lo <= i <= hi) ==> post.lower.l2_owner(page_map_ptr, i) is None
        &&& forall|i: L2Index| #![trigger post.lower.l2_owner(page_map_ptr, i)]
            lo <= i <= hi ==> post.lower.l2_owner(page_map_ptr, i) is Write && post.lower.l2_owner(page_map_ptr, i)->Write_thread_id == thread_id
        &&& post.lower.pagetable_window_locks == Map::new(
            pre.lower.pagetable_window_locks.dom() + Set::<usize>::range(0, 512).map_by(|i: usize| WindowVa { va: spec_index2va((target_l4i, target_l3i, i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
            |w: WindowVa| if pre.lower.pagetable_window_locks.dom().contains(w) { pre.lower.pagetable_window_locks[w] } else if lo <= spec_v2l2index(w.va) <= hi { LockStateU::WriteLocked { writer: thread_id } } else { LockStateU::Unlocked })
    }

    /// EOF closure of `create_entry_l3`: every page-table invariant leaf.
    pub(super) proof fn create_entry_l3_eof(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            TABLE_TYPE == PT_TYPE,
            KERNEL_MEM_END_L4INDEX <= target_l4i,
            pei_valid(hi),
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            post.wf(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::create_entry_l3_eof_higher_inv(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        Self::create_entry_l3_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        Self::create_entry_l3_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        Self::create_entry_l3_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        Self::create_entry_l3_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        Self::create_entry_l3_eof_wf_window_locks_va(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        Self::create_entry_l3_eof_wf_window_locks_slot(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        Self::create_entry_l3_eof_wf_window_locks(post);
        Self::create_entry_l3_eof_hidden_l1_tables_in_locked_windows(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
    }

    /// EOF closure of `create_entry_l3`: `hidden_l1_tables_in_locked_windows`. The new L2 page owns no L1 page.
    proof fn create_entry_l3_eof_hidden_l1_tables_in_locked_windows(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr,
        lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    { reveal(WholePageTable::create_entry_l3_eof_transition_framing); }

    /// EOF closure of `create_entry_l3`: the big-lock invariant.
    proof fn create_entry_l3_eof_higher_inv(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            post.higher.inv(),
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        assert(post.higher.wf_l4()) by { reveal(PageTableHigher::wf_l4); };
        assert(post.higher.wf_l3()) by { reveal(PageTableHigher::wf_l3); };
        assert(post.higher.disjoint_l4()) by { reveal(PageTableHigher::disjoint_l4); };
        assert(post.higher.disjoint_l3()) by { reveal(PageTableHigher::disjoint_l3); reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.higher.wf_mapping_1g()) by { reveal(PageTableHigher::wf_mapping_1g); reveal(PageTableHigher::wf_l4); };
        assert(post.higher.user_only()) by { reveal(PageTableHigher::user_only); };
        assert(post.higher.rwx_upper_level_entries()) by { reveal(PageTableHigher::rwx_upper_level_entries); };
        assert(post.higher.table_pages_wf()) by { reveal(PageTableHigher::table_pages_wf); };
        assert(post.higher.tables_reachable_wf()) by { reveal(PageTableHigher::tables_reachable_wf); };
        assert(post.higher.kernel_entries_wf()) by { reveal(PageTableHigher::kernel_entries_wf); };
    }

    /// EOF closure of `create_entry_l3`: the table-shape leaves of the window half.
    proof fn create_entry_l3_eof_table_leaves(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.va_addr_valid(),
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
    }

    /// EOF closure of `create_entry_l3`: `wf_mapping_4k`.
    proof fn create_entry_l3_eof_wf_mapping_4k(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            post.wf_mapping_4k(),
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); };
    }

    /// EOF closure of `create_entry_l3`: `wf_mapping_2m`.
    proof fn create_entry_l3_eof_wf_mapping_2m(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            post.wf_mapping_2m(),
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); };
    }

    /// EOF closure of `create_entry_l3`: `tables_reachable_wf`.
    proof fn create_entry_l3_eof_tables_reachable_wf(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(PageTableHigher::disjoint_l4); };
    }

    /// EOF closure of `create_entry_l3`: the window-map half of `wf_window_locks`. Proved apart from the L2-slot half:
    /// one query over both halves costs several times the two separate ones. `tables_reachable_wf` maps each L2 page's
    /// reverse index back to the page, which ends the window/slot trigger chain of `wf_window_locks`.
    proof fn create_entry_l3_eof_wf_window_locks_va(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            TABLE_TYPE == PT_TYPE,
            KERNEL_MEM_END_L4INDEX <= target_l4i,
            pei_valid(hi),
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            forall|w: WindowVa| #![trigger post.lower.pagetable_window_locks.dom().contains(w)] post.lower.pagetable_window_locks.dom().contains(w) ==> {
                &&& page_table_key_2m_valid::<TABLE_TYPE>(w.va)
                &&& post.kernel_l4_end() <= spec_v2l4index(w.va)
                &&& post.window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                &&& post.lower.pagetable_window_locks.spec_index(w) == if post.lower.l2_owner(post.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)) is Write {
                    LockStateU::WriteLocked { writer: post.lower.l2_owner(post.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))->Write_thread_id }
                } else {
                    LockStateU::Unlocked
                }
            },
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        reveal(WholePageTable::wf_window_locks); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::tables_reachable_wf);
        spec_index2va_injective();
        broadcast use spec_va_2m_valid_index_roundtrip, iova_2m_valid_index_roundtrip, spec_index2va_2m_valid;
    }

    /// EOF closure of `create_entry_l3`: the L2-slot half of `wf_window_locks`.
    proof fn create_entry_l3_eof_wf_window_locks_slot(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            TABLE_TYPE == PT_TYPE,
            KERNEL_MEM_END_L4INDEX <= target_l4i,
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            page_ptr_valid(page_map_ptr),
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            forall|p: PageMapPtr, i: L2Index|
                #![trigger post.lower.l2_owner(p, i)]
                #![trigger post.lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((post.higher.l2_rev_map.view().spec_index(p).0, post.higher.l2_rev_map.view().spec_index(p).1, i, 0)) })]
                post.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> {
                    let (l4i, l3i) = post.higher.l2_rev_map.view().spec_index(p);
                    if post.spec_resolve_mapping_l3(l4i, l3i) is Some {
                        post.lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((l4i, l3i, i, 0)) })
                    } else {
                        post.lower.l2_owner(p, i) is None
                    }
                },
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        reveal(WholePageTable::wf_window_locks); reveal(WholePageTable::tables_reachable_wf); reveal(PageTableHigher::wf_l4); reveal(PageTableHigher::disjoint_l4);
        spec_index2va_injective();
        broadcast use spec_index2va_2m_valid, spec_va_2m_valid_index_roundtrip;
    }

    /// EOF closure of `create_entry_l3`: `wf_window_locks` from its two halves.
    proof fn create_entry_l3_eof_wf_window_locks(post: Self)
        requires
            forall|w: WindowVa| #![trigger post.lower.pagetable_window_locks.dom().contains(w)] post.lower.pagetable_window_locks.dom().contains(w) ==> {
                &&& page_table_key_2m_valid::<TABLE_TYPE>(w.va)
                &&& post.kernel_l4_end() <= spec_v2l4index(w.va)
                &&& post.window_exists(spec_v2l4index(w.va), spec_v2l3index(w.va))
                &&& post.lower.pagetable_window_locks.spec_index(w) == if post.lower.l2_owner(post.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)) is Write {
                    LockStateU::WriteLocked { writer: post.lower.l2_owner(post.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))->Write_thread_id }
                } else {
                    LockStateU::Unlocked
                }
            },
            forall|p: PageMapPtr, i: L2Index|
                #![trigger post.lower.l2_owner(p, i)]
                #![trigger post.lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((post.higher.l2_rev_map.view().spec_index(p).0, post.higher.l2_rev_map.view().spec_index(p).1, i, 0)) })]
                post.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> {
                    let (l4i, l3i) = post.higher.l2_rev_map.view().spec_index(p);
                    if post.spec_resolve_mapping_l3(l4i, l3i) is Some {
                        post.lower.pagetable_window_locks.dom().contains(WindowVa { va: spec_index2va((l4i, l3i, i, 0)) })
                    } else {
                        post.lower.l2_owner(p, i) is None
                    }
                },
        ensures
            post.wf_window_locks(),
    {
        reveal(WholePageTable::wf_window_locks);
    }

    /// Operation-state summary of `create_entry_l2`: entry `target_l2i` of L2 page `target_l2_p` now links the new empty L1 page
    /// `page_map_ptr`, which joins the L1 pages with reverse index `(target_l4i, target_l3i, target_l2i)`; the big-lock payload, the
    /// window locks, and every other field are unchanged.
    #[verifier::opaque]
    pub open spec fn create_entry_l2_eof_transition_framing(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr) -> bool {
        &&& post.higher == pre.higher
        &&& post.lower == (PageTableLower { l2_perms: post.lower.l2_perms, l1_rev_map: post.lower.l1_rev_map, ..pre.lower })
        &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
        &&& forall|p: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(p)] p != target_l2_p ==> post.lower.l2_perms.spec_index(p) == pre.lower.l2_perms.spec_index(p)
        &&& post.lower.l2_perms.spec_index(target_l2_p).addr() == target_l2_p && post.lower.l2_perms.spec_index(target_l2_p).is_init()
        &&& post.lower.l2_page(target_l2_p).addr() == target_l2_p
        &&& post.lower.l2_page(target_l2_p).wf()
        &&& forall|p: PageMapPtr, i: L2Index| #![trigger post.lower.l2_page(p).entry_lock(i)]
            p == target_l2_p && i != target_l2i ==> post.lower.l2_page(p).entry_lock(i) == pre.lower.l2_page(p).entry_lock(i)
        &&& post.lower.l2_entry(target_l2_p, target_l2i) =~= (PageEntry {
            addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } })
        &&& post.lower.l2_owner(target_l2_p, target_l2i) == pre.lower.l2_owner(target_l2_p, target_l2i)
        &&& post.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is Some
        &&& post.lower.l1_perm(target_l2_p, target_l2i).addr() == page_map_ptr
        &&& post.lower.l1_perm(target_l2_p, target_l2i).is_init()
        &&& post.lower.l1_page(target_l2_p, target_l2i).wf()
        &&& forall|p: PageMapPtr, i: L2Index, j: L1Index| #![trigger post.lower.l1_page(p, i).spec_index(j)]
            p == target_l2_p && pei_valid(j) ==> if i == target_l2i { post.lower.l1_page(p, i).spec_index(j).is_empty() } else { post.lower.l1_page(p, i).spec_index(j) == pre.lower.l1_page(p, i).spec_index(j) }
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
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.wf(),
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    {
        Self::create_entry_l2_eof_higher_inv(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_table_leaves(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_mapping_4k(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_mapping_2m(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_tables_reachable_wf(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_wf_window_locks(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
        Self::create_entry_l2_eof_hidden_l1_tables_in_locked_windows(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr);
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
        reveal(WholePageTable::create_entry_l2_eof_transition_framing);
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
            post.l3_links_l2_wf(),
            post.wf_l2(),
            post.wf_l1(),
            post.disjoint_l2(),
            post.user_only(),
            post.rwx_upper_level_entries(),
            post.table_pages_wf(),
            post.va_addr_valid(),
    {
        reveal(WholePageTable::create_entry_l2_eof_transition_framing);
        assert(post.l3_links_l2_wf()) by { reveal(WholePageTable::l3_links_l2_wf); };
        assert(post.wf_l2()) by { reveal(WholePageTable::wf_l2); };
        assert(post.wf_l1()) by { reveal(WholePageTable::wf_l1); };
        assert(post.disjoint_l2()) by { reveal(WholePageTable::disjoint_l2); reveal(WholePageTable::wf_l2); };
        assert(post.user_only()) by { reveal(WholePageTable::user_only); };
        assert(post.rwx_upper_level_entries()) by { reveal(WholePageTable::rwx_upper_level_entries); };
        assert(post.table_pages_wf()) by { reveal(WholePageTable::table_pages_wf); };
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
        reveal(WholePageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_mapping_4k()) by { reveal(WholePageTable::wf_mapping_4k); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::wf_l2); };
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
        reveal(WholePageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_mapping_2m()) by { reveal(WholePageTable::wf_mapping_2m); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); };
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
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            post.tables_reachable_wf(),
    {
        reveal(WholePageTable::create_entry_l2_eof_transition_framing);
        assert(post.tables_reachable_wf()) by { reveal(WholePageTable::tables_reachable_wf); reveal(PageTableHigher::wf_l4); reveal(WholePageTable::l3_links_l2_wf); reveal(WholePageTable::wf_l2); broadcast use PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at; };
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
        reveal(WholePageTable::create_entry_l2_eof_transition_framing);
        assert(post.wf_window_locks()) by { reveal(WholePageTable::wf_window_locks); };
    }

    /// EOF closure of `create_entry_l2`: `hidden_l1_tables_in_locked_windows`. The new link is present.
    proof fn create_entry_l2_eof_hidden_l1_tables_in_locked_windows(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr)
        requires
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
    { reveal(WholePageTable::create_entry_l2_eof_transition_framing); }

    /// EOF closure of `create_entry_l4`: the new root entry holds the empty L3 page; the rest of the held chain is unchanged.
    pub(super) proof fn create_entry_l4_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) && l4i != target_l4i ==> post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
            post.spec_held_l4(target_l4i) == Some(PageEntry { addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: false } }),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_held_l3(l4i, l3i) == pre.spec_held_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_held_1g_l3(l4i, l3i) == pre.spec_held_1g_l3(l4i, l3i),
    {
        Self::create_entry_l4_eof_held_1g(pre, post, target_l4i, page_map_ptr);
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `create_entry_l4`: every held 1G leaf is unchanged; the new L3 page holds none.
    proof fn create_entry_l4_eof_held_1g(pre: Self, post: Self, target_l4i: L4Index, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pre.spec_held_l4(target_l4i) is None,
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l4_eof_transition_framing(pre, post, target_l4i, page_map_ptr),
        ensures
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_held_1g_l3(l4i, l3i) == pre.spec_held_1g_l3(l4i, l3i),
    {
        reveal(WholePageTable::create_entry_l4_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
    }

    /// EOF closure of `create_entry_l3`: the new L3 entry holds the empty L2 page; every other root and L3 entry is held as before.
    proof fn create_entry_l3_eof_held_l3(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_held_l3(l4i, l3i) == pre.spec_held_l3(l4i, l3i),
            post.spec_held_l3(target_l4i, target_l3i) == Some(PageEntry { addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } }),
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
        reveal(PageTableHigher::disjoint_l4);
    }

    /// EOF closure of `create_entry_l3`: the new L3 entry holds the empty L2 page; the rest of the held chain is unchanged.
    pub(super) proof fn create_entry_l3_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            forall|l4i: L4Index| #![trigger post.spec_held_l4(l4i)] pre.kernel_l4_end() <= l4i && pei_valid(l4i) ==> post.spec_held_l4(l4i) == pre.spec_held_l4(l4i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && (l4i, l3i) != (target_l4i, target_l3i) ==> post.spec_held_l3(l4i, l3i) == pre.spec_held_l3(l4i, l3i),
            post.spec_held_l3(target_l4i, target_l3i) == Some(PageEntry { addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } }),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_held_1g_l3(l4i, l3i) == pre.spec_held_1g_l3(l4i, l3i),
    {
        Self::create_entry_l3_eof_held_1g(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        Self::create_entry_l3_eof_held_l3(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id);
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
        reveal(WholePageTable::l3_links_l2_wf);
    }

    /// EOF closure of `create_entry_l3`: every held 1G leaf is unchanged; the target entry held none and now links an L2 page.
    proof fn create_entry_l3_eof_held_1g(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l3_p: PageMapPtr, page_map_ptr: PageMapPtr, lo: L2Index, hi: L2Index, thread_id: LockThreadId)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pre.spec_resolve_mapping_l4(target_l4i) is Some,
            pre.spec_resolve_mapping_l4(target_l4i)->0.addr == target_l3_p,
            pre.spec_held_l3(target_l4i, target_l3i) is None,
            pre.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) is None,
            pre.page_closure().contains(page_map_ptr) == false,
            Self::create_entry_l3_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l3_p, page_map_ptr, lo, hi, thread_id),
        ensures
            forall|l4i: L4Index, l3i: L3Index| #![trigger post.spec_held_1g_l3(l4i, l3i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> post.spec_held_1g_l3(l4i, l3i) == pre.spec_held_1g_l3(l4i, l3i),
    {
        reveal(WholePageTable::create_entry_l3_eof_transition_framing);
        reveal(PageTableHigher::wf_l4);
        assert(pre.spec_held_1g_l3(target_l4i, target_l3i) is None);
    }

    /// EOF closure of `create_entry_l2`: the new L2 entry holds the empty L1 page; the rest of the held chain is unchanged.
    pub(super) proof fn create_entry_l2_eof_held_chain(pre: Self, post: Self, target_l4i: L4Index, target_l3i: L3Index, target_l2i: L2Index, target_l2_p: PageMapPtr, page_map_ptr: PageMapPtr)
        requires
            pre.wf(),
            pre.kernel_l4_end() <= target_l4i && pei_valid(target_l4i),
            pei_valid(target_l3i),
            pei_valid(target_l2i),
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i) is Some,
            pre.spec_resolve_mapping_l3(target_l4i, target_l3i)->0.addr == target_l2_p,
            pre.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) is None,
            pre.lower.l2_page(target_l2_p).entry_lock(target_l2i).l1() is None,
            Self::create_entry_l2_eof_transition_framing(pre, post, target_l4i, target_l3i, target_l2i, target_l2_p, page_map_ptr),
        ensures
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && (l4i, l3i, l2i) != (target_l4i, target_l3i, target_l2i) ==> post.spec_held_l2(l4i, l3i, l2i) == pre.spec_held_l2(l4i, l3i, l2i),
            post.spec_held_l2(target_l4i, target_l3i, target_l2i) == Some(PageEntry { addr: page_map_ptr, perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true, kernel_present: true } }),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index| #![trigger post.spec_held_4k_l1(l4i, l3i, l2i, l1i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) ==> post.spec_held_4k_l1(l4i, l3i, l2i, l1i) == pre.spec_held_4k_l1(l4i, l3i, l2i, l1i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger post.spec_held_2m_l2(l4i, l3i, l2i)]
                pre.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) ==> post.spec_held_2m_l2(l4i, l3i, l2i) == pre.spec_held_2m_l2(l4i, l3i, l2i),
    {
        reveal(WholePageTable::create_entry_l2_eof_transition_framing);
        broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
        pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(target_l4i, target_l3i);
    }
}
} // verus!
