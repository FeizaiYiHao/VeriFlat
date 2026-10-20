use vstd::prelude::*;
verus! {
use crate::*;

/// `lock_window` moved only the lock bit of window `(l4i, l3i, l2i)`, now owned by `thread_id`, and added its base
/// address to `locked_windows`.
pub open spec fn lock_window_eof_transition_framing(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    lock_token: LockToken) -> bool
{
    let p = pre.window_l2_page(l4i, l3i);
    &&& post.higher == pre.higher
    &&& post.lower.l2_perms == pre.lower.l2_perms
    &&& post.lower.l2_ghost == pre.lower.l2_ghost
    &&& post.lower.l1_rev_map == pre.lower.l1_rev_map
    &&& post.lower.l1_tables == pre.lower.l1_tables
    &&& post.lower.mapping_4k == pre.lower.mapping_4k
    &&& post.lower.mapping_2m == pre.lower.mapping_2m
    &&& post.lower.l2_lock == pre.lower.l2_lock.insert(p, post.lower.l2_lock_of(p))
    &&& post.lower.l2_lock.dom() =~= pre.lower.l2_lock.dom()
    &&& post.lower.l2_lock_of(p).addr() == pre.lower.l2_lock_of(p).addr()
    &&& post.lower.l2_lock_of(p).wf()
    &&& forall|i: usize| #![trigger post.lower.l2_lock_of(p).lock_state(i)] pei_valid(i) && i != l2i ==> post.lower.l2_lock_of(p).lock_state(i) == pre.lower.l2_lock_of(p).lock_state(i)
    &&& post.lower.l2_lock_of(p).lock_state(l2i) == (SpinLockState::Some { thread_id, lock_id: lock_token })
    &&& post.lower.locked_windows == pre.lower.locked_windows.insert(spec_index2va((l4i, l3i, l2i, 0)))
}

/// `unlock_window` cleared only the lock bit of window `(l4i, l3i, l2i)` and dropped its base address from
/// `locked_windows`.
pub open spec fn unlock_window_eof_transition_framing(pre: PageTableC<PT_TYPE>, post: PageTableC<PT_TYPE>, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool {
    let p = pre.window_l2_page(l4i, l3i);
    &&& post.higher == pre.higher
    &&& post.lower.l2_perms == pre.lower.l2_perms
    &&& post.lower.l2_ghost == pre.lower.l2_ghost
    &&& post.lower.l1_rev_map == pre.lower.l1_rev_map
    &&& post.lower.l1_tables == pre.lower.l1_tables
    &&& post.lower.mapping_4k == pre.lower.mapping_4k
    &&& post.lower.mapping_2m == pre.lower.mapping_2m
    &&& post.lower.l2_lock == pre.lower.l2_lock.insert(p, post.lower.l2_lock_of(p))
    &&& post.lower.l2_lock.dom() =~= pre.lower.l2_lock.dom()
    &&& post.lower.l2_lock_of(p).addr() == pre.lower.l2_lock_of(p).addr()
    &&& post.lower.l2_lock_of(p).wf()
    &&& forall|i: usize| #![trigger post.lower.l2_lock_of(p).lock_state(i)] pei_valid(i) && i != l2i ==> post.lower.l2_lock_of(p).lock_state(i) == pre.lower.l2_lock_of(p).lock_state(i)
    &&& post.lower.l2_lock_of(p).lock_state(l2i) is None
    &&& post.lower.locked_windows == pre.lower.locked_windows.remove(spec_index2va((l4i, l3i, l2i, 0)))
}

/// EOF closure of `lock_window`.
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
    assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
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
    broadcast use spec_va_2m_valid_index_roundtrip;
    let va = spec_index2va((l4i, l3i, l2i, 0));
    let p = pre.window_l2_page(l4i, l3i);
    assert(pre.lower.l2_perms.dom().contains(p)) by { pre.higher.wf_l4_at(l4i); pre.wf_l3_at(pre.spec_resolve_mapping_l4(l4i)->0.addr, l3i); };
    let rev = pre.higher.l2_rev_map.view().spec_index(p);
    assert(rev == (l4i, l3i)) by { pre.tables_reachable_wf_l2_at(p); pre.higher.resolve_l3_addr_unique_at(l4i, l3i, rev.0, rev.1); };
    assert(spec_v2l4index(va) == l4i && spec_v2l3index(va) == l3i && spec_v2l2index(va) == l2i) by { spec_index2va_injective(); };
    reveal(PageTableC::wf_window_locks);
}

/// EOF closure of `unlock_window`.
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
    assert(post.l2_tokens_paired()) by { reveal(PageTableC::l2_tokens_paired); };
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
    reveal(PageTableC::tables_reachable_wf);
    spec_index2va_injective();
    reveal(PageTableC::wf_window_locks);
}
} // verus!
