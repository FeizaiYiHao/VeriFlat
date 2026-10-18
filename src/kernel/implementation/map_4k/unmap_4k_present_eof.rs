use vstd::prelude::*;
use crate::*;

verus! {
/// Clears the present bit of the 4K leaf `va` in `pagetable`; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn clear_4k_mapping_present_eof_transition_framing(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr) -> bool {
    let old_pt = pre.pt_mp.spec_index(pagetable);
    let new_pt = post.pt_mp.spec_index(pagetable);
    &&& post == (KernelK { pt_mp: post.pt_mp, ..pre })
    &&& post.pt_mp.unchanged_except(&pre.pt_mp, pagetable)
    &&& new_pt.locking_thread() == old_pt.locking_thread()
    &&& new_pt.being_killed() == old_pt.being_killed()
    &&& new_pt.view().mapping_4k() == old_pt.view().mapping_4k().insert(va, MapEntry { present: false, ..old_pt.view().mapping_4k().spec_index(va) })
    &&& new_pt.view().mapping_2m() == old_pt.view().mapping_2m()
    &&& new_pt.view().mapping_1g() == old_pt.view().mapping_1g()
    &&& new_pt.view().page_closure() == old_pt.view().page_closure()
    &&& new_pt.view().kernel_entries == old_pt.view().kernel_entries
    &&& new_pt.view().kernel_l4_end == old_pt.view().kernel_l4_end
    &&& new_pt.view().cr3 == old_pt.view().cr3
    &&& new_pt.view().pcid == old_pt.view().pcid
    &&& new_pt.view().proc_ptr == old_pt.view().proc_ptr
}

pub(super) proof fn clear_4k_mapping_present_eof(pre: KernelK, post: KernelK, pagetable: RwLockPageTableRoot, va: VAddr)
    requires
        pre.inv(),
        clear_4k_mapping_present_eof_transition_framing(pre, post, pagetable, va),
        pre.pt_mp.dom().contains(pagetable),
        pre.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(va),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable).inv(),
        post.pt_mp.spec_index(pagetable).locking_thread() is Write,
    ensures post.inv(),
{
    reveal(clear_4k_mapping_present_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(pagetable_perms_wf); reveal(pagetable_hidden_leaves_only_when_wlocked); reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(pagetable_pages_wf(post.pt_mp, post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, post.pt_mp, pre.pg_arr, post.pg_arr); };
        assert(page_pagetable_wf(post.pt_mp, post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
        assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); };
}
}
