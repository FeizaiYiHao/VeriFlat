use vstd::prelude::*;
use crate::*;

verus! {
/// Clears the present bit of the 4K leaf `iova` in IOMMU table `iommu_table`; every other kernel field is unchanged.
#[verifier::opaque]
pub(super) open spec fn clear_iommu_4k_mapping_present_eof_transition_framing(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr) -> bool {
    let old_it = pre.it_mp.spec_index(iommu_table);
    let new_it = post.it_mp.spec_index(iommu_table);
    &&& post == (KernelK { it_mp: post.it_mp, ..pre })
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table)
    &&& new_it.locking_thread() == old_it.locking_thread()
    &&& new_it.being_killed() == old_it.being_killed()
    &&& new_it.view().mapping_4k() == old_it.view().mapping_4k().insert(iova, MapEntry { present: false, ..old_it.view().mapping_4k().spec_index(iova) })
    &&& new_it.view().mapping_2m() == old_it.view().mapping_2m()
    &&& new_it.view().mapping_1g() == old_it.view().mapping_1g()
    &&& new_it.view().page_closure() == old_it.view().page_closure()
    &&& new_it.view().kernel_entries == old_it.view().kernel_entries
    &&& new_it.view().kernel_l4_end == old_it.view().kernel_l4_end
    &&& new_it.view().cr3 == old_it.view().cr3
    &&& new_it.view().pcid == old_it.view().pcid
    &&& new_it.view().proc_ptr == old_it.view().proc_ptr
}

pub(super) proof fn clear_iommu_4k_mapping_present_eof(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr)
    requires
        pre.inv(),
        clear_iommu_4k_mapping_present_eof_transition_framing(pre, post, iommu_table, iova),
        pre.it_mp.dom().contains(iommu_table),
        pre.it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(iova),
        pre.it_mp.spec_index(iommu_table).locking_thread() is Write,
        post.it_mp.perms_wf(),
        post.it_mp.spec_index(iommu_table).inv(),
    ensures post.inv(),
{
    reveal(clear_iommu_4k_mapping_present_eof_transition_framing);
    assert(post.subsystems_inv()) by { reveal(iommu_table_perms_wf); reveal(iommu_table_hidden_leaves_only_when_wlocked); reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); };
        assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
        assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_match); };
        assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_table_lock_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); };
}
}
