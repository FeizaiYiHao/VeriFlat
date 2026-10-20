use vstd::prelude::*;
use crate::*;

verus! {
/// Closes `inv()` after `wlock_pagetable`, `rlock_pagetable`, and `runlock_pagetable`: only the target table's lock state
/// moved; it was not write-locked, so its leaves and TLB entries are present.
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
        post.pt_mp.spec_index(pagetable_ptr).view_ghost() == pre.pt_mp.spec_index(pagetable_ptr).view_ghost(),
        post.pt_mp.spec_index(pagetable_ptr).being_killed() == pre.pt_mp.spec_index(pagetable_ptr).being_killed(),
        post.pt_mp.spec_index(pagetable_ptr).killer_info() == pre.pt_mp.spec_index(pagetable_ptr).killer_info(),
        !pre.pt_mp.spec_index(pagetable_ptr).wlocked(),
    ensures
        post.inv(),
        pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable_ptr, post.pt_mp.spec_index(pagetable_ptr).view()),
        post.pt_mp.spec_index(pagetable_ptr).view().leaves_present(),
{
    assert(pagetable_tlb_entries_present(post.cpu_tlb, post.cpu_arr, post.pcid_needflush, pagetable_ptr, post.pt_mp.spec_index(pagetable_ptr).view())) by { reveal(tlb_wf_spec); };
    assert(post.pt_mp.spec_index(pagetable_ptr).view().leaves_present()) by { reveal(pagetable_perms_wf); reveal(pagetable_hidden_leaves_only_when_wlocked); };
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp)) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pagetable_ptr); };
    assert(post.subsystems_inv()) by { lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { lemma_tlb_wf_spec_preserved_for_pagetable_invariant_fields_forall(); };
}

/// Closes `inv()` after `wunlock_pagetable`: the released table's leaves and TLB entries are present.
pub(super) proof fn wunlock_pagetable_eof(pre: KernelK, post: KernelK, pagetable_ptr: RwLockPageTableRoot)
    requires
        pre.inv(),
        pre.pt_mp.dom().contains(pagetable_ptr),
        pagetable_tlb_entries_present(pre.cpu_tlb, pre.cpu_arr, pre.pcid_needflush, pagetable_ptr, pre.pt_mp.spec_index(pagetable_ptr).view()),
        pre.pt_mp.spec_index(pagetable_ptr).view().leaves_present(),
        post == (KernelK { pt_mp: post.pt_mp, ..pre }),
        post.pt_mp.perms_wf(),
        post.pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr),
        wunlock_ensures(pre.pt_mp.spec_index(pagetable_ptr), post.pt_mp.spec_index(pagetable_ptr)),
    ensures
        post.inv(),
{
    assert(pagetable_invariant_fields_unchanged(pre.pt_mp, post.pt_mp)) by { pagetable_lock_op_preserves_invariant_fields(pre.pt_mp, post.pt_mp, pagetable_ptr); };
    assert(post.subsystems_inv()) by { lemma_pagetable_perms_wf_preserved_for_lock_op_forall(); reveal(KernelK::default_pagetable_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
    assert(post.memory_management_inv()) by {
        process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post);
        lemma_process_pagetable_match_preserved_for_pagetable_invariant_fields_forall();
        lemma_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_container_process_page_pagetable_wf_preserved_for_pagetable_invariant_fields_forall();
        lemma_pagetable_pages_wf_preserved_for_pagetable_invariant_fields_forall();
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_pagetable_invariant_fields_forall(); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
} // verus!
