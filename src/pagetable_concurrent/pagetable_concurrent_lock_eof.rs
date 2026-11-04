use vstd::prelude::*;
verus! {
use crate::*;

/// `lock_window` moved only the owner of entry `l2i` of the window's L2 page, free before and now `thread_id`, and
/// marked the window write-locked in `pagetable_window_locks`; every other L2 page, entry and lower field is untouched.
pub open spec fn lock_window_eof_transition_framing(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    lock_token: LockToken) -> bool
{
    let p = pre.window_l2_page(l4i, l3i);
    &&& post.higher == pre.higher
    &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
    &&& forall|q: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(q)] q != p ==> post.lower.l2_perms.spec_index(q) == pre.lower.l2_perms.spec_index(q)
    &&& post.lower.l2_perms.spec_index(p).addr() == pre.lower.l2_perms.spec_index(p).addr()
    &&& post.lower.l2_perms.spec_index(p).is_init()
    &&& post.lower.l2_page(p).addr() == pre.lower.l2_page(p).addr()
    &&& forall|j: L2Index| #![trigger post.lower.l2_page(p).entry_lock(j)] j != l2i ==> post.lower.l2_page(p).entry_lock(j) == pre.lower.l2_page(p).entry_lock(j)
    &&& post.lower.l2_entry(p, l2i) == pre.lower.l2_entry(p, l2i)
    &&& post.lower.l2_page(p).entry_lock(l2i).l1() == pre.lower.l2_page(p).entry_lock(l2i).l1()
    &&& pre.lower.l2_owner(p, l2i) is None
    &&& post.lower.l2_owner(p, l2i) == (RwLockState::Write { thread_id, lock_id: lock_token })
    &&& post.lower.pagetable_window_locks == pre.lower.pagetable_window_locks.insert(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }, LockStateU::WriteLocked)
    &&& post.lower.l1_rev_map == pre.lower.l1_rev_map
    &&& post.lower.mapping_4k == pre.lower.mapping_4k
    &&& post.lower.mapping_2m == pre.lower.mapping_2m
    &&& post.lower.window_stale_cpus == pre.lower.window_stale_cpus
}

/// `unlock_window` cleared only the owner of entry `l2i` of the window's L2 page and marked the window unlocked in
/// `pagetable_window_locks`; every other L2 page, entry and lower field is untouched.
pub open spec fn unlock_window_eof_transition_framing(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool {
    let p = pre.window_l2_page(l4i, l3i);
    &&& post.higher == pre.higher
    &&& post.lower.l2_perms.dom() == pre.lower.l2_perms.dom()
    &&& forall|q: PageMapPtr| #![trigger post.lower.l2_perms.spec_index(q)] q != p ==> post.lower.l2_perms.spec_index(q) == pre.lower.l2_perms.spec_index(q)
    &&& post.lower.l2_perms.spec_index(p).addr() == pre.lower.l2_perms.spec_index(p).addr()
    &&& post.lower.l2_perms.spec_index(p).is_init()
    &&& post.lower.l2_page(p).addr() == pre.lower.l2_page(p).addr()
    &&& forall|j: L2Index| #![trigger post.lower.l2_page(p).entry_lock(j)] j != l2i ==> post.lower.l2_page(p).entry_lock(j) == pre.lower.l2_page(p).entry_lock(j)
    &&& post.lower.l2_entry(p, l2i) == pre.lower.l2_entry(p, l2i)
    &&& post.lower.l2_page(p).entry_lock(l2i).l1() == pre.lower.l2_page(p).entry_lock(l2i).l1()
    &&& post.lower.l2_owner(p, l2i) is None
    &&& post.lower.pagetable_window_locks == pre.lower.pagetable_window_locks.insert(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }, LockStateU::Unlocked)
    &&& post.lower.l1_rev_map == pre.lower.l1_rev_map
    &&& post.lower.mapping_4k == pre.lower.mapping_4k
    &&& post.lower.mapping_2m == pre.lower.mapping_2m
    &&& post.lower.window_stale_cpus == pre.lower.window_stale_cpus
}

/// EOF closure of `lock_window`: re-establishes `WholePageTable::wf` from its per-leaf `lock_window_eof_*` closures.
pub(super) proof fn lock_window_eof(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        pre.kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        page_table_key_2m_valid::<PT_TYPE>(spec_index2va((l4i, l3i, l2i, 0))),
        pre.window_exists(l4i, l3i),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.wf(),
{
    lock_window_eof_wf_l3(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_wf_l2(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_wf_l1(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_disjoint_l2(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_wf_mapping_4k(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_wf_mapping_2m(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_user_only(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_rwx_upper_level_entries(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_table_pages_wf(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_tables_reachable_wf(pre, post, l4i, l3i, l2i, thread_id, lock_token);
    lock_window_eof_window_locks(pre, post, l4i, l3i, l2i, thread_id, lock_token);
}

/// EOF closure of `lock_window` for `wf_window_locks`: the new owner is the window the reverse map records for its
/// L2 page.
proof fn lock_window_eof_window_locks(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    lock_token: LockToken)
    requires
        pre.wf(),
        pre.kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        page_table_key_2m_valid::<PT_TYPE>(spec_index2va((l4i, l3i, l2i, 0))),
        pre.window_exists(l4i, l3i),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.wf_window_locks(),
{
    broadcast use {PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at, spec_va_2m_valid_index_roundtrip};
    let va = spec_index2va((l4i, l3i, l2i, 0));
    assert(spec_v2l4index(va) == l4i && spec_v2l3index(va) == l3i && spec_v2l2index(va) == l2i) by { spec_index2va_injective(); };
    let p = pre.window_l2_page(l4i, l3i);
    assert(pre.lower.l2_perms.dom().contains(p)) by { pre.higher.wf_l4_at(l4i); pre.l3_links_l2_wf_at(pre.spec_resolve_mapping_l4(l4i)->0.addr, l3i); };
    let rev = pre.higher.l2_rev_map.view().spec_index(p);
    assert(rev == (l4i, l3i)) by { pre.tables_reachable_wf_l2_at(p); pre.higher.disjoint_l4_l3_implies_held_l3_addr_unique_at(l4i, l3i, rev.0, rev.1); };
    reveal(WholePageTable::wf_window_locks);
}

/// EOF closure of `unlock_window`: re-establishes `WholePageTable::wf` from its per-leaf `unlock_window_eof_*` closures.
pub(super) proof fn unlock_window_eof(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        pre.kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        pre.window_exists(l4i, l3i),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.wf(),
{
    unlock_window_eof_wf_l3(pre, post, l4i, l3i, l2i);
    unlock_window_eof_wf_l2(pre, post, l4i, l3i, l2i);
    unlock_window_eof_wf_l1(pre, post, l4i, l3i, l2i);
    unlock_window_eof_disjoint_l2(pre, post, l4i, l3i, l2i);
    unlock_window_eof_wf_mapping_4k(pre, post, l4i, l3i, l2i);
    unlock_window_eof_wf_mapping_2m(pre, post, l4i, l3i, l2i);
    unlock_window_eof_user_only(pre, post, l4i, l3i, l2i);
    unlock_window_eof_rwx_upper_level_entries(pre, post, l4i, l3i, l2i);
    unlock_window_eof_table_pages_wf(pre, post, l4i, l3i, l2i);
    unlock_window_eof_tables_reachable_wf(pre, post, l4i, l3i, l2i);
    unlock_window_eof_window_locks(pre, post, l4i, l3i, l2i);
}

/// EOF closure of `unlock_window` for `wf_window_locks`: the released base address belongs to no other locked
/// window.
proof fn unlock_window_eof_window_locks(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        pre.kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        pre.window_exists(l4i, l3i),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.wf_window_locks(),
{
    broadcast use {PageTableHigher::disjoint_l4_l3_implies_resolve_l3_addr_unique_at, spec_va_2m_valid_index_roundtrip};
    let p = pre.window_l2_page(l4i, l3i);
    assert(pre.lower.l2_perms.dom().contains(p)) by { pre.higher.wf_l4_at(l4i); pre.l3_links_l2_wf_at(pre.spec_resolve_mapping_l4(l4i)->0.addr, l3i); };
    let rev = pre.higher.l2_rev_map.view().spec_index(p);
    assert(rev == (l4i, l3i)) by { pre.tables_reachable_wf_l2_at(p); pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(l4i, l3i); pre.higher.disjoint_l4_l3_implies_held_l3_addr_unique_at(l4i, l3i, rev.0, rev.1); };
    pre.wf_window_locks_l2_entry_at(p, l2i);
    spec_index2va_injective();
    reveal(WholePageTable::wf_window_locks);
}

/// EOF closure of `lock_window` for `l3_links_l2_wf`.
proof fn lock_window_eof_wf_l3(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.l3_links_l2_wf(),
{ reveal(WholePageTable::l3_links_l2_wf); }

/// EOF closure of `lock_window` for `wf_l2`.
proof fn lock_window_eof_wf_l2(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.wf_l2(),
{ reveal(WholePageTable::wf_l2); }

/// EOF closure of `lock_window` for `wf_l1`.
proof fn lock_window_eof_wf_l1(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.wf_l1(),
{ reveal(WholePageTable::wf_l1); }

/// EOF closure of `lock_window` for `disjoint_l2`.
proof fn lock_window_eof_disjoint_l2(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.disjoint_l2(),
{ reveal(WholePageTable::disjoint_l2); }

/// EOF closure of `lock_window` for `wf_mapping_4k`.
proof fn lock_window_eof_wf_mapping_4k(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.wf_mapping_4k(),
{ reveal(WholePageTable::wf_mapping_4k); }

/// EOF closure of `lock_window` for `wf_mapping_2m`.
proof fn lock_window_eof_wf_mapping_2m(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.wf_mapping_2m(),
{ reveal(WholePageTable::wf_mapping_2m); }

/// EOF closure of `lock_window` for `user_only`.
proof fn lock_window_eof_user_only(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.user_only(),
{ reveal(WholePageTable::user_only); }

/// EOF closure of `lock_window` for `rwx_upper_level_entries`.
proof fn lock_window_eof_rwx_upper_level_entries(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.rwx_upper_level_entries(),
{ reveal(WholePageTable::rwx_upper_level_entries); }

/// EOF closure of `lock_window` for `table_pages_wf`.
proof fn lock_window_eof_table_pages_wf(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.table_pages_wf(),
{ reveal(WholePageTable::table_pages_wf); }

/// EOF closure of `lock_window` for `tables_reachable_wf`.
proof fn lock_window_eof_tables_reachable_wf(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.tables_reachable_wf(),
{ reveal(WholePageTable::tables_reachable_wf); }

/// EOF closure of `unlock_window` for `l3_links_l2_wf`.
proof fn unlock_window_eof_wf_l3(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.l3_links_l2_wf(),
{ reveal(WholePageTable::l3_links_l2_wf); }

/// EOF closure of `unlock_window` for `wf_l2`.
proof fn unlock_window_eof_wf_l2(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.wf_l2(),
{ reveal(WholePageTable::wf_l2); }

/// EOF closure of `unlock_window` for `wf_l1`.
proof fn unlock_window_eof_wf_l1(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.wf_l1(),
{ reveal(WholePageTable::wf_l1); }

/// EOF closure of `unlock_window` for `disjoint_l2`.
proof fn unlock_window_eof_disjoint_l2(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.disjoint_l2(),
{ reveal(WholePageTable::disjoint_l2); }

/// EOF closure of `unlock_window` for `wf_mapping_4k`.
proof fn unlock_window_eof_wf_mapping_4k(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.wf_mapping_4k(),
{ reveal(WholePageTable::wf_mapping_4k); }

/// EOF closure of `unlock_window` for `wf_mapping_2m`.
proof fn unlock_window_eof_wf_mapping_2m(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.wf_mapping_2m(),
{ reveal(WholePageTable::wf_mapping_2m); }

/// EOF closure of `unlock_window` for `user_only`.
proof fn unlock_window_eof_user_only(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.user_only(),
{ reveal(WholePageTable::user_only); }

/// EOF closure of `unlock_window` for `rwx_upper_level_entries`.
proof fn unlock_window_eof_rwx_upper_level_entries(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.rwx_upper_level_entries(),
{ reveal(WholePageTable::rwx_upper_level_entries); }

/// EOF closure of `unlock_window` for `table_pages_wf`.
proof fn unlock_window_eof_table_pages_wf(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.table_pages_wf(),
{ reveal(WholePageTable::table_pages_wf); }

/// EOF closure of `unlock_window` for `tables_reachable_wf`.
proof fn unlock_window_eof_tables_reachable_wf(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        post.tables_reachable_wf(),
{ reveal(WholePageTable::tables_reachable_wf); }

/// EOF closure of `lock_window` for `hidden_l1_tables_in_locked_windows`: the window's entry is now write-locked.
pub(super) proof fn lock_window_eof_hidden_l1_tables_in_locked_windows(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index,
    thread_id: LockThreadId, lock_token: LockToken)
    requires
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        pre.lower.hidden_l1_tables_in_locked_windows() ==> post.lower.hidden_l1_tables_in_locked_windows(),
{}

/// EOF closure of `unlock_window` for `hidden_l1_tables_in_locked_windows`: the released entry hides no L1 page.
pub(super) proof fn unlock_window_eof_hidden_l1_tables_in_locked_windows(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        pre.lower.hidden_l1_tables_in_locked_windows() && !pre.lower.l2_entry_hides_l1(pre.window_l2_page(l4i, l3i), l2i) ==> post.lower.hidden_l1_tables_in_locked_windows(),
{}

/// EOF closure of `lock_window` for the held chain: only the window's lock owner moved.
pub(super) proof fn lock_window_eof_held_chain(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
    requires
        pre.wf(),
        pre.kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        pre.window_exists(l4i, l3i),
        lock_window_eof_transition_framing(pre, post, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        forall|l4j: L4Index, l3j: L3Index, l2j: L2Index| #![trigger post.spec_held_l2(l4j, l3j, l2j)]
            pre.kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j) && pei_valid(l2j) ==> post.spec_held_l2(l4j, l3j, l2j) == pre.spec_held_l2(l4j, l3j, l2j),
        forall|l4j: L4Index, l3j: L3Index, l2j: L2Index, l1j: L1Index| #![trigger post.spec_held_4k_l1(l4j, l3j, l2j, l1j)]
            pre.kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j) && pei_valid(l2j) && pei_valid(l1j) ==> post.spec_held_4k_l1(l4j, l3j, l2j, l1j) == pre.spec_held_4k_l1(l4j, l3j, l2j, l1j),
        forall|l4j: L4Index, l3j: L3Index, l2j: L2Index| #![trigger post.spec_held_2m_l2(l4j, l3j, l2j)]
            pre.kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j) && pei_valid(l2j) ==> post.spec_held_2m_l2(l4j, l3j, l2j) == pre.spec_held_2m_l2(l4j, l3j, l2j),
{
    broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
    pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(l4i, l3i);
}

/// EOF closure of `unlock_window` for the held chain: only the window's lock owner moved.
pub(super) proof fn unlock_window_eof_held_chain(pre: WholePageTable<PT_TYPE>, post: WholePageTable<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.wf(),
        pre.kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        pei_valid(l2i),
        pre.window_exists(l4i, l3i),
        unlock_window_eof_transition_framing(pre, post, l4i, l3i, l2i),
    ensures
        forall|l4j: L4Index, l3j: L3Index, l2j: L2Index| #![trigger post.spec_held_l2(l4j, l3j, l2j)]
            pre.kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j) && pei_valid(l2j) ==> post.spec_held_l2(l4j, l3j, l2j) == pre.spec_held_l2(l4j, l3j, l2j),
        forall|l4j: L4Index, l3j: L3Index, l2j: L2Index, l1j: L1Index| #![trigger post.spec_held_4k_l1(l4j, l3j, l2j, l1j)]
            pre.kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j) && pei_valid(l2j) && pei_valid(l1j) ==> post.spec_held_4k_l1(l4j, l3j, l2j, l1j) == pre.spec_held_4k_l1(l4j, l3j, l2j, l1j),
        forall|l4j: L4Index, l3j: L3Index, l2j: L2Index| #![trigger post.spec_held_2m_l2(l4j, l3j, l2j)]
            pre.kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j) && pei_valid(l2j) ==> post.spec_held_2m_l2(l4j, l3j, l2j) == pre.spec_held_2m_l2(l4j, l3j, l2j),
{
    broadcast use PageTableHigher::disjoint_l4_l3_implies_held_l3_addr_unique_at;
    pre.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(l4i, l3i);
}
} // verus!
