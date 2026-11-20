use vstd::prelude::*;
use crate::*;

verus! {
/// Disables the raw R/W bits at `iova`, keeping its historical mapping until flush; other kernel fields stay.
#[verifier::opaque]
pub(super) open spec fn clear_iommu_4k_mapping_present_eof_transition_framing(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot, iova: VAddr) -> bool {
    let old_it = pre.it_mp.spec_index(iommu_table);
    let new_it = post.it_mp.spec_index(iommu_table);
    &&& post == (KernelK { it_mp: post.it_mp, ..pre })
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table)
    &&& new_it.locking_thread() == old_it.locking_thread()
    &&& new_it.being_killed() == old_it.being_killed()
    &&& new_it.view().spec_resolve_mapping_4k_l1(spec_v2l4index(iova), spec_v2l3index(iova), spec_v2l2index(iova), spec_v2l1index(iova)) is Some
    &&& !new_it.view().spec_resolve_mapping_4k_l1(spec_v2l4index(iova), spec_v2l3index(iova), spec_v2l2index(iova), spec_v2l1index(iova))->0.perm.present
    &&& !new_it.view().spec_resolve_mapping_4k_l1(spec_v2l4index(iova), spec_v2l3index(iova), spec_v2l2index(iova), spec_v2l1index(iova))->0.perm.write
    &&& new_it.view().mapping_4k() == old_it.view().mapping_4k().insert(iova, MapEntry { present: false, ..old_it.view().mapping_4k().spec_index(iova) })
    &&& new_it.view().mapping_2m() == old_it.view().mapping_2m()
    &&& new_it.view().mapping_1g() == old_it.view().mapping_1g()
    &&& new_it.view().page_closure() == old_it.view().page_closure()
    &&& new_it.view().kernel_entries == old_it.view().kernel_entries
    &&& new_it.view().kernel_l4_end == old_it.view().kernel_l4_end
    &&& new_it.view().cr3 == old_it.view().cr3
    &&& new_it.view().pcid == old_it.view().pcid
    &&& new_it.view().proc_ptr == old_it.view().proc_ptr
    &&& new_it.view().did == old_it.view().did
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
        iommu_table_perms_wf(post.it_mp),
    ensures
        post.inv(),
        pre.it_mp.spec_index(iommu_table).view().did is None ==> iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table),
{
    reveal(clear_iommu_4k_mapping_present_eof_transition_framing);
    assert(pagetable_pci_mappings_wf(post.pci_bars.view(), post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_pci_mappings_wf); };
    assert(post.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    assert(post.memory_management_inv()) by {
        assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
        assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); };
        assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
        assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
        assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_iommu_table_wf); };
        assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
    assert(pre.it_mp.spec_index(iommu_table).view().did is None ==> iommu_table_tlb_entries_present(post.iommu_tlb, post.irt.view(), post.it_mp, iommu_table)) by { reveal(iommu_table_tlb_entries_present); };
}
}
