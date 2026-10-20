use vstd::prelude::*;
use crate::*;
use crate::pagetable_concurrent::pagetable_concurrent_lock_eof::*;

verus! {
/// `lock_pagetable_window` moved only the window half of table `root`: window `(l4i, l3i, l2i)` is now owned by
/// `thread_id`, every other window keeps its holder, a write-held table's ghost slot follows its window half, and the
/// leaves and table pages are unchanged.
#[verifier::opaque]
pub open spec fn lock_pagetable_window_eof_transition_framing(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index,
    thread_id: LockThreadId, lock_token: LockToken) -> bool
{
    let before = pagetable_c(pre.pt_mp, pre.pt_lower.view(), root);
    let after = pagetable_c(post.pt_mp, post.pt_lower.view(), root);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root))
    &&& post.pt_lower.view().dom() =~= pre.pt_lower.view().dom()
    &&& lock_window_eof_transition_framing(before, after, l4i, l3i, l2i, thread_id, lock_token)
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.page_closure() == before.page_closure()
    &&& after.leaves_present() == before.leaves_present()
    &&& forall|pagetable_ptr: RwLockPageTableRoot|
        #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr)]
        pre.pt_mp.dom().contains(pagetable_ptr) && pagetable_ptr != root ==> pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr)
    &&& forall|l4: L4Index, l3: L3Index, l2: L2Index, t: LockThreadId|
        #![trigger after.window_locked_by_thread(l4, l3, l2, t)]
        before.kernel_l4_end() <= l4 && pei_valid(l4) && pei_valid(l3) && pei_valid(l2) ==> after.window_locked_by_thread(l4, l3, l2, t)
            == if l4 == l4i && l3 == l3i && l2 == l2i { t == thread_id } else { before.window_locked_by_thread(l4, l3, l2, t) }
}

/// `unlock_pagetable_window` moved only the window half of table `root`: window `(l4i, l3i, l2i)` is free, every other
/// window keeps its holder, a write-held table's ghost slot follows its window half, and the leaves and table pages
/// are unchanged.
#[verifier::opaque]
pub open spec fn unlock_pagetable_window_eof_transition_framing(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool {
    let before = pagetable_c(pre.pt_mp, pre.pt_lower.view(), root);
    let after = pagetable_c(post.pt_mp, post.pt_lower.view(), root);
    &&& post == (KernelK { pt_mp: post.pt_mp, pt_lower: post.pt_lower, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, root)
    &&& update_ghost_ensures(pre.pt_mp.spec_index(root), post.pt_mp.spec_index(root),
        if pre.pt_mp.spec_index(root).wlocked() { post.pt_lower.view().spec_index(root) } else { pre.pt_mp.spec_index(root).view_ghost() })
    &&& post.pt_lower.view() =~= pre.pt_lower.view().insert(root, post.pt_lower.view().spec_index(root))
    &&& post.pt_lower.view().dom() =~= pre.pt_lower.view().dom()
    &&& unlock_window_eof_transition_framing(before, after, l4i, l3i, l2i)
    &&& after.mapping_4k() == before.mapping_4k()
    &&& after.mapping_2m() == before.mapping_2m()
    &&& after.mapping_1g() == before.mapping_1g()
    &&& after.page_closure() == before.page_closure()
    &&& after.leaves_present() == before.leaves_present()
    &&& forall|pagetable_ptr: RwLockPageTableRoot|
        #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr)]
        pre.pt_mp.dom().contains(pagetable_ptr) && pagetable_ptr != root ==> pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr)
    &&& forall|l4: L4Index, l3: L3Index, l2: L2Index, t: LockThreadId|
        #![trigger after.window_locked_by_thread(l4, l3, l2, t)]
        before.kernel_l4_end() <= l4 && pei_valid(l4) && pei_valid(l3) && pei_valid(l2) ==> after.window_locked_by_thread(l4, l3, l2, t)
            == (!(l4 == l4i && l3 == l3i && l2 == l2i) && before.window_locked_by_thread(l4, l3, l2, t))
}

/// Closes `inv()` after `lock_pagetable_window`: the new window owner holds the table's big lock and nothing a table
/// invariant reads besides window ownership moved.
pub(super) proof fn lock_pagetable_window_eof(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index, thread_id: LockThreadId,
    lock_token: LockToken)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        pre.pt_mp.spec_index(root).locked_by_thread(thread_id),
        post.pt_mp.perms_wf(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), root).wf(),
        lock_pagetable_window_eof_transition_framing(pre, post, root, l4i, l3i, l2i, thread_id, lock_token),
    ensures
        post.inv(),
{
    reveal(lock_pagetable_window_eof_transition_framing);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pre.pt_lower.view(), root);
    assert(pagetable_perms_wf(post.pt_mp)) by { lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
}

/// Closes `inv()` after `unlock_pagetable_window`: releasing a window only drops one window owner, and nothing a
/// table invariant reads besides window ownership moved.
pub(super) proof fn unlock_pagetable_window_eof(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l2i: L2Index)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(root),
        post.pt_mp.perms_wf(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), root).wf(),
        unlock_pagetable_window_eof_transition_framing(pre, post, root, l4i, l3i, l2i),
    ensures
        post.inv(),
{
    reveal(unlock_pagetable_window_eof_transition_framing);
    pagetable_perms_wf_at(pre.pt_mp, root);
    pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pre.pt_lower.view(), root);
    assert(pagetable_perms_wf(post.pt_mp)) by { lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_holders_hold_pagetable); };
    assert(pagetable_hidden_leaves_only_when_wlocked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
}
} // verus!
