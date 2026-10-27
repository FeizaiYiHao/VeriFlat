use vstd::prelude::*;
use crate::*;

verus! {
/// Attaching a function owned by the live process `process_ptr` to its write-held IOMMU table `table` keeps every
/// invariant: the entry carries the table's root and DID, which the table keeps or, on first attach, adopts from the
/// function's candidate domain, empty while that candidate was unanchored. Every cpu, process, thread, and container
/// field is as before.
pub(super) proof fn pci_attach_dma_eof(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, table: RwLockPageTableRoot, bus: usize, device: usize, function: usize)
    requires
        pre.inv(),
        post == (KernelK { irt: post.irt, it_mp: post.it_mp, ..pre }),
        post.irt.inv(),
        pci_bdf_valid(bus, device, function),
        pre.it_mp.dom().contains(table),
        post.it_mp.unchanged_except(&pre.it_mp, table),
        {
            let before = pre.it_mp.spec_index(table).view();
            let did = if before.did is Some { before.did.unwrap() } else { pci_bdf_did(bus, device, function) };
            &&& vtd_domain_id_valid(did)
            &&& post.it_mp.spec_index(table).view() == (PageTable { did: Some(did), ..before })
            &&& post.it_mp.spec_index(table).view().page_closure() == before.page_closure()
            &&& post.it_mp.spec_index(table).view().mapping_4k() == before.mapping_4k()
            &&& post.it_mp.spec_index(table).view().mapping_2m() == before.mapping_2m()
            &&& post.it_mp.spec_index(table).view().mapping_1g() == before.mapping_1g()
            &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] #![trigger post.irt.view().spec_index_iommu_root(b, d, f)]
                #![trigger post.irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
                &&& post.irt.view().spec_index_owner(b, d, f) == pre.irt.view().spec_index_owner(b, d, f)
                &&& post.irt.view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { Some(before.cr3) } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
                &&& post.irt.view().spec_index_iommu_did(b, d, f) == if (b, d, f) == (bus, device, function) { Some(did) } else { pre.irt.view().spec_index_iommu_did(b, d, f) }
            }
        },
        post.irt.view().owners() == pre.irt.view().owners(),
        iommu_table_perms_wf(post.it_mp),
        post.it_mp.spec_index(table).locking_thread() == pre.it_mp.spec_index(table).locking_thread(),
        post.it_mp.spec_index(table).being_killed() == pre.it_mp.spec_index(table).being_killed(),
        pre.it_mp.spec_index(table).locking_thread() is Write,
        pre.it_mp.spec_index(table).view().leaves_present(),
        pre.prc_mp.dom().contains(process_ptr),
        pre.prc_mp.spec_index(process_ptr).view().iommu_table == Some(table),
        pre.irt.view().spec_index_owner(bus, device, function) == process_ptr,
        pre.irt.view().spec_index_iommu_root(bus, device, function) is None,
    ensures
        post.inv(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post),
        post.it_mp.spec_index(table).view().leaves_present(),
{
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &post)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by {
        reveal(process_emptied_tables_wf); reveal(process_iommu_table_match);
    };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { reveal(process_kernel_pages_owner_wf); reveal(iommu_table_pages_wf); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by {
        reveal(iommu_root_table_process_wf); reveal(process_iommu_table_match);
    };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by {
        reveal(iommu_tlb_wf_spec); reveal(IommuTLB::inv); reveal(iommu_root_table_process_wf); reveal(process_iommu_table_match); pre.irt.view().context_wf_at(bus, device, function);
    };
    assert(post.inv()) by { reveal(KernelK::default_pagetable_wf); };
}
} // verus!
