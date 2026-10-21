use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_pagetable` and `rlock_pagetable`: only the target table's lock state moved and every
/// holder kept it, a new writer's ghost slot backs up the window half; it was not write-locked, so its hidden leaves lie in
/// locked windows, and if it was not locked at all no window of it is held, so its leaves and TLB entries are present and
/// it lists no stale CPU.
pub(super) proof fn pagetable_lock_state_eof(pre: KernelK, post: KernelK, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        post == (KernelK { pt_mp: post.pt_mp, ..pre }),
        post.pt_mp.perms_wf(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).inv(),
        post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view(),
        post.pt_mp.spec_index(pagetable_ptr).view_rodata() == pre.pt_mp.spec_index(pagetable_ptr).view_rodata(),
        post.pt_mp.spec_index(pagetable_ptr).wlocked() ==> post.pt_mp.spec_index(pagetable_ptr).view_ghost() == post.pt_lower.view().spec_index(pagetable_ptr),
        post.pt_mp.spec_index(pagetable_ptr).being_killed() == pre.pt_mp.spec_index(pagetable_ptr).being_killed(),
        post.pt_mp.spec_index(pagetable_ptr).killer_info() == pre.pt_mp.spec_index(pagetable_ptr).killer_info(),
        !pre.pt_mp.spec_index(pagetable_ptr).wlocked(),
        forall|thread_id: LockThreadId|
            #![trigger post.pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id)]
            pre.pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id) ==> post.pt_mp.spec_index(pagetable_ptr).locked_by_thread(thread_id),
    ensures
        post.inv(),
        pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).hidden_leaves_in_locked_windows(),
        !pre.pt_mp.spec_index(pagetable_ptr).locked() ==> pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).leaves_present(),
        !pre.pt_mp.spec_index(pagetable_ptr).locked()
            ==> pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable_ptr, pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr)),
        !pre.pt_mp.spec_index(pagetable_ptr).locked() ==> pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
{
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp, post.pt_lower.view())) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), pagetable_ptr); };
    assert(!pre.pt_mp.spec_index(pagetable_ptr).locked() ==> pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).leaves_present()) by {
        pagetable_hidden_leaves_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
        pre.default_pagetable_wf_at(pagetable_ptr); reveal(pagetable_window_holders_hold_pagetable); broadcast use spec_va_4k_valid_index_roundtrip;
    };
    assert(pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr).hidden_leaves_in_locked_windows()) by { pagetable_hidden_leaves_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr); };
    assert(!pre.pt_mp.spec_index(pagetable_ptr).locked()
        ==> pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable_ptr, pagetable_c(post.pt_mp, post.pt_lower.view(), pagetable_ptr))) by {
        if !pre.pt_mp.spec_index(pagetable_ptr).locked() { tlb_wf_pagetable_entries_present_at(pre, pagetable_ptr); }
    };
    assert(!pre.pt_mp.spec_index(pagetable_ptr).locked() ==> pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus =~= Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()) by {
        broadcast use pagetable_unlocked_stale_key_absent_at;
    };
    assert(post.subsystems_inv()) by {
        lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf);
        reveal(pagetable_window_holders_hold_pagetable); reveal(pagetable_hidden_leaves_only_when_locked); reveal(pagetable_window_stale_cpus_only_when_locked);
    };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
}

/// A page table that no thread locks lists no stale CPU under key `k`: a listed window is locked, and its holder would
/// hold the table.
broadcast proof fn pagetable_unlocked_stale_key_absent_at(pre: KernelK, pagetable_ptr: RwLockPageTableRoot, k: (PageMapPtr, L2Index))
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        !pre.pt_mp.spec_index(pagetable_ptr).locked(),
    ensures !#[trigger] pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus.dom().contains(k),
{
    let c = pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
    if c.lower.window_stale_cpus.dom().contains(k) {
        pagetable_lower_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr);
        pagetable_window_stale_cpus_only_when_locked_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr, k.0, k.1);
        reveal(PageTableC::l2_tokens_paired); reveal(PageTableC::tables_reachable_wf);
        let (l4i, l3i) = c.higher.l2_rev_map.view().spec_index(k.0);
        pagetable_window_holders_hold_pagetable_at(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr, l4i, l3i, k.1, c.lower.l2_lock_of(k.0).lock_state(k.1)->Some_thread_id);
    }
}

/// Closes `inv()` after `runlock_pagetable`: the releasing reader holds no window of the table, every other holder
/// keeps it, and the table stays out of write mode, so its hidden leaves stay in locked windows.
pub(super) proof fn runlock_pagetable_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        post == (KernelK { pt_mp: post.pt_mp, ..pre }),
        post.pt_mp.perms_wf(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        pre.pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(pre_lctx.thread_id()),
        runlock_ensures(pre.pt_mp.spec_index(pagetable_ptr), post.pt_mp.spec_index(pagetable_ptr), pre_lctx.thread_id()),
        pagetable_window_typed_lock_map_aligned(pre.pt_mp, pre.pt_lower.view(), pre_lctx.pagetable_window_lock_map(), pre_lctx.pagetable_lock_map(), pre_lctx.thread_id()),
        forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] !pre_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)),
    ensures
        post.inv(),
{
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp, post.pt_lower.view())) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), pagetable_ptr); };
    assert(post.subsystems_inv()) by {
        lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf); reveal(pagetable_hidden_leaves_only_when_locked);
        reveal(pagetable_window_holders_hold_pagetable); reveal(pagetable_window_typed_lock_map_aligned); reveal(pagetable_window_stale_cpus_only_when_locked);
    };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
}

/// Closes `inv()` after `wunlock_pagetable`: the writer holds no window of the released table, so no thread does, the
/// table's leaves are present, and it lists no stale CPU.
pub(super) proof fn wunlock_pagetable_eof(pre: KernelK, post: KernelK, pre_lctx: LocalContext, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).leaves_present(),
        post == (KernelK { pt_mp: post.pt_mp, ..pre }),
        post.pt_mp.perms_wf(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        pre.pt_mp.spec_index(pagetable_ptr).wlocked_by_thread(pre_lctx.thread_id()),
        wunlock_ensures(pre.pt_mp.spec_index(pagetable_ptr), post.pt_mp.spec_index(pagetable_ptr)),
        pagetable_window_typed_lock_map_aligned(pre.pt_mp, pre.pt_lower.view(), pre_lctx.pagetable_window_lock_map(), pre_lctx.pagetable_lock_map(), pre_lctx.thread_id()),
        forall|w: WindowVa| #![trigger pre_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] !pre_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, w)),
    ensures
        post.inv(),
{
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp, post.pt_lower.view())) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), pagetable_ptr); };
    assert(post.subsystems_inv()) by {
        lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf); reveal(pagetable_hidden_leaves_only_when_locked);
        reveal(pagetable_window_holders_hold_pagetable); reveal(pagetable_window_typed_lock_map_aligned); reveal(pagetable_window_stale_cpus_only_when_locked);
    };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
}

/// `downgrade_pagetable` moved only the lock of table `pagetable_ptr`: `thread_id`'s write lock became its sole read
/// lock under the same token, and the payload, ghost slot, kill state, and window half stayed.
#[verifier::opaque]
pub open spec fn downgrade_pagetable_eof_transition_framing(pre: KernelK, post: KernelK, thread_id: LockThreadId, pagetable_ptr: RwLockPageTableRoot) -> bool {
    &&& post == (KernelK { pt_mp: post.pt_mp, ..pre })
    &&& post.pt_mp.perms_wf()
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
    &&& pre.pt_mp.spec_index(pagetable_ptr).wlocked_by_thread(thread_id)
    &&& post.pt_mp.spec_index(pagetable_ptr).locking_thread() == RwLockState::Read {
        reader_map: Map::empty().insert(thread_id, pre.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id) }
    &&& post.pt_mp.spec_index(pagetable_ptr).inv()
    &&& post.pt_mp.spec_index(pagetable_ptr).view() == pre.pt_mp.spec_index(pagetable_ptr).view()
    &&& post.pt_mp.spec_index(pagetable_ptr).view_rodata() == pre.pt_mp.spec_index(pagetable_ptr).view_rodata()
    &&& post.pt_mp.spec_index(pagetable_ptr).view_ghost() == pre.pt_mp.spec_index(pagetable_ptr).view_ghost()
    &&& post.pt_mp.spec_index(pagetable_ptr).being_killed() == pre.pt_mp.spec_index(pagetable_ptr).being_killed()
    &&& post.pt_mp.spec_index(pagetable_ptr).killer_info() == pre.pt_mp.spec_index(pagetable_ptr).killer_info()
}

/// Closes `inv()` after `downgrade_pagetable`: the holder keeps the table in read mode, so every window owner still
/// holds it, the table's leaves are present, and it lists no stale CPU, so no table invariant needs a writer.
pub(super) proof fn downgrade_pagetable_eof(pre: KernelK, post: KernelK, thread_id: LockThreadId, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).leaves_present(),
        pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        downgrade_pagetable_eof_transition_framing(pre, post, thread_id, pagetable_ptr),
    ensures
        post.inv(),
{
    reveal(downgrade_pagetable_eof_transition_framing);
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp, post.pt_lower.view())) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, post.pt_lower.view(), pagetable_ptr); };
    assert(post.subsystems_inv()) by {
        lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); reveal(pagetable_lower_wf); reveal(pagetable_hidden_leaves_only_when_locked);
        reveal(pagetable_window_holders_hold_pagetable); reveal(pagetable_window_stale_cpus_only_when_locked);
    };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
}
} // verus!
