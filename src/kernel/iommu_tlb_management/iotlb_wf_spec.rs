use vstd::prelude::*;

verus! {
use crate::*;

/// The global IOTLB is indexed by DID.  In the current identity model DID is
/// the 16-bit BDF encoding, so the static root table selects the unique owner
/// and the owner's one IOMMU table without a CPU dirty bitmap.  Ownership and
/// root/table agreement live in `iommu_root_table_process_wf`; this predicate
/// only constrains the cached translations.  A cached context entry equals the
/// current entry and exists only for a present root (`CAP.CM = 0`).  Detach
/// clears the entry and invalidates in the same section under the root-table
/// lock, so the predicate holds again at the section end.  The IOMMU table's
/// write lock is the dirty marker: an attached domain of a table that is not
/// write-locked caches only present leaves.  The write holder may hide leaves
/// while attached and re-establishes this with an IOTLB flush before unlocking.
// Proof dependency (confirmed): iommu_root_table_process_wf.
#[verifier::opaque]
pub open spec fn iommu_tlb_wf_spec(iommu_tlb: IommuTLB, root_table: IommuRootTable, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap) -> bool {
    &&& iommu_tlb.inv()
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        #![trigger root_table.spec_index_iommu_root(bus, device, function)]
        #![trigger iommu_tlb.spec_index(pci_bdf_did(bus, device, function))]
        pci_bdf_valid(bus, device, function) ==> {
            let did = pci_bdf_did(bus, device, function);
            let domain_tlb = iommu_tlb.spec_index(did);
            let proc_ptr = root_table.spec_index_owner(bus, device, function);
            let iommu_root = root_table.spec_index_iommu_root(bus, device, function);
            let iommu_table = iommu_table_map.spec_index(process_map.spec_index(proc_ptr).view().iommu_table.unwrap());
            &&& vtd_domain_id_valid(did)
            &&& iommu_root is None ==> domain_tlb.is_empty()
            &&& iommu_root is Some ==> single_tlb_subset_of_pagetable(domain_tlb, iommu_table.view())
            &&& iommu_root is Some && !(iommu_table.locking_thread() is Write) ==> single_tlb_subset_of_present_pagetable(domain_tlb, iommu_table.view())
            &&& iommu_tlb.context_cache().dom().contains(did) ==> iommu_root == Some(iommu_tlb.context_cache()[did])
        }
}

/// Every IOTLB domain attached to IOMMU table `it` caches only present leaves of `it`: the write holder's flush establishes it and the step boundary keeps it.
/// Opaque: callers forward it unchanged; only the flush producer and the EOF closures that relate it to `iommu_tlb_wf_spec` reveal it.
#[verifier::opaque]
pub open spec fn iommu_table_tlb_entries_present(iommu_tlb: IommuTLB, root_table: IommuRootTable, iommu_table_map: IommuTableLockedMap, it: RwLockPageTableRoot) -> bool {
    forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_iommu_root(bus, device, function)]
        #![trigger root_table.spec_index_owner(bus, device, function)]
        pci_bdf_valid(bus, device, function) && root_table.spec_index_iommu_root(bus, device, function) is Some && iommu_table_map.spec_index(it).view().proc_ptr == root_table.spec_index_owner(bus, device, function)
            ==> single_tlb_subset_of_present_pagetable(iommu_tlb.spec_index(pci_bdf_did(bus, device, function)), iommu_table_map.spec_index(it).view())
}
}
