use vstd::prelude::*;
verus! {
use crate::*;

/// `lock_window` moved only the owner of entry `l2i` of the window's L2 page, free before and now `thread_id`, and
/// marked the window write-locked in `pagetable_window_locks`; every other L2 page, entry and lower field is untouched.
pub open spec fn lock_window_eof_transition_framing(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
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
    &&& post.lower.l2_owner(p, l2i) == (SpinLockState::Some { thread_id, lock_id: lock_token })
    &&& post.lower.pagetable_window_locks == pre.lower.pagetable_window_locks.insert(WindowVa { va: spec_index2va((l4i, l3i, l2i, 0)) }, LockStateU::WriteLocked)
    &&& post.lower.l1_rev_map == pre.lower.l1_rev_map
    &&& post.lower.mapping_4k == pre.lower.mapping_4k
    &&& post.lower.mapping_2m == pre.lower.mapping_2m
    &&& post.lower.window_stale_cpus == pre.lower.window_stale_cpus
}

/// `unlock_window` cleared only the owner of entry `l2i` of the window's L2 page and marked the window unlocked in
/// `pagetable_window_locks`; every other L2 page, entry and lower field is untouched.
pub open spec fn unlock_window_eof_transition_framing(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool {
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

/// EOF closure of `lock_window`: re-establishes `PageTableC::wf`, with `wf_window_locks` from `lock_window_eof_window_locks`.
pub(super) proof fn lock_window_eof(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId, lock_token: LockToken)
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
    assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
    assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
    assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
    assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
    assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); };
    assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); };
    assert(post.user_only()) by { reveal(PageTableC::user_only); };
    assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
    assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
    assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); };
    assert(post.wf_window_locks()) by { lock_window_eof_window_locks(pre, post, l4i, l3i, l2i, thread_id, lock_token); };
}

/// EOF closure of `lock_window` for `wf_window_locks`: the new owner is the window the reverse map records for its
/// L2 page.
proof fn lock_window_eof_window_locks(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
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
    broadcast use {PageTableHigher::resolve_l3_addr_unique_at, spec_va_2m_valid_index_roundtrip};
    let va = spec_index2va((l4i, l3i, l2i, 0));
    assert(spec_v2l4index(va) == l4i && spec_v2l3index(va) == l3i && spec_v2l2index(va) == l2i) by { spec_index2va_injective(); };
    reveal(PageTableC::wf_window_locks);
}

/// EOF closure of `unlock_window`: re-establishes `PageTableC::wf`, with `wf_window_locks` from `unlock_window_eof_window_locks`.
pub(super) proof fn unlock_window_eof(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
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
    assert(post.wf_l3()) by { reveal(PageTableC::wf_l3); };
    assert(post.wf_l2()) by { reveal(PageTableC::wf_l2); };
    assert(post.wf_l1()) by { reveal(PageTableC::wf_l1); };
    assert(post.disjoint_l2()) by { reveal(PageTableC::disjoint_l2); };
    assert(post.wf_mapping_4k()) by { reveal(PageTableC::wf_mapping_4k); };
    assert(post.wf_mapping_2m()) by { reveal(PageTableC::wf_mapping_2m); };
    assert(post.user_only()) by { reveal(PageTableC::user_only); };
    assert(post.rwx_upper_level_entries()) by { reveal(PageTableC::rwx_upper_level_entries); };
    assert(post.table_pages_wf()) by { reveal(PageTableC::table_pages_wf); };
    assert(post.tables_reachable_wf()) by { reveal(PageTableC::tables_reachable_wf); };
    assert(post.wf_window_locks()) by { unlock_window_eof_window_locks(pre, post, l4i, l3i, l2i); };
}

/// EOF closure of `unlock_window` for `wf_window_locks`: the released base address belongs to no other locked
/// window.
proof fn unlock_window_eof_window_locks(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index)
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
    broadcast use {PageTableHigher::resolve_l3_addr_unique_at, spec_va_2m_valid_index_roundtrip};
    let p = pre.window_l2_page(l4i, l3i);
    assert(pre.lower.l2_perms.dom().contains(p)) by { pre.higher.wf_l4_at(l4i); pre.wf_l3_at(pre.spec_resolve_mapping_l4(l4i)->0.addr, l3i); };
    let rev = pre.higher.l2_rev_map.view().spec_index(p);
    assert(rev == (l4i, l3i)) by { pre.tables_reachable_wf_l2_at(p); pre.higher.resolve_l3_addr_unique_at(l4i, l3i, rev.0, rev.1); };
    pre.wf_window_locks_slot_at(p, l2i);
    spec_index2va_injective();
    reveal(PageTableC::wf_window_locks);
}
} // verus!
