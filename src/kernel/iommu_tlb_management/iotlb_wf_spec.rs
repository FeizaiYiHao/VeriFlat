use vstd::prelude::*;

verus! {
use crate::*;

/// The global IOTLB is indexed by DID and the context cache by B/D/F.  Ownership,
/// root/table/DID agreement, and DID anchoring live in `iommu_root_table_process_wf`;
/// this predicate only constrains cached state.  A cached context entry equals the
/// current present entry's root and DID (`CAP.CM = 0`).  A present entry's DID
/// domain is its owner table's DID domain.  A candidate DID whose anchor
/// `pci_bdf_of_did(did)` does not carry it is inactive, and its domain is empty.
/// Detach clears the entry and invalidates its DID in the same section under the
/// root-table lock, so the predicate holds again at the section end.  The IOMMU
/// table's write lock is the dirty marker: an attached domain of a table that is
/// not write-locked caches only present leaves.  The write holder may hide leaves
/// while attached and re-establishes this with an IOTLB flush before unlocking.
// Proof dependency (confirmed): iommu_root_table_process_wf.
#[verifier::opaque]
pub open spec fn iommu_tlb_wf_spec(iommu_tlb: IommuTLB, root_table: IommuRootTable, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap) -> bool {
    &&& iommu_tlb.inv()
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        #![trigger root_table.spec_index_iommu_root(bus, device, function)]
        pci_bdf_valid(bus, device, function) && root_table.spec_index_iommu_root(bus, device, function) is Some ==> {
            let proc_ptr = root_table.spec_index_owner(bus, device, function);
            let iommu_table = iommu_table_map.spec_index(process_map.spec_index(proc_ptr).view().iommu_table.unwrap());
            let domain_tlb = iommu_tlb.spec_index(iommu_table.view().did->Some_0);
            &&& single_tlb_subset_of_pagetable(domain_tlb, iommu_table.view())
            &&& !(iommu_table.locking_thread() is Write) ==> single_tlb_subset_of_present_pagetable(domain_tlb, iommu_table.view())
        }
    &&& forall|did: VtdDomainId|
        #![trigger iommu_tlb.spec_index(did)]
        vtd_domain_id_valid(did) ==> {
            let anchor = pci_bdf_of_did(did);
            root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) != Some(did) ==> iommu_tlb.spec_index(did).is_empty()
        }
    &&& forall|bdf: PciBdf|
        #![trigger iommu_tlb.context_cache().dom().contains(bdf)]
        iommu_tlb.context_cache().dom().contains(bdf) ==> {
            &&& root_table.spec_index_iommu_root(bdf.0, bdf.1, bdf.2) == Some(iommu_tlb.context_cache()[bdf].0)
            &&& root_table.spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == Some(iommu_tlb.context_cache()[bdf].1)
        }
}

/// The DID domain of IOMMU table `it` caches only present leaves of `it`: the write holder's flush establishes it and the
/// step boundary keeps it.  A table without a DID constrains nothing; its domain-emptiness lives in `iommu_tlb_wf_spec`.
/// Opaque: callers forward it unchanged; only the flush producer and the EOF closures that relate it to `iommu_tlb_wf_spec` reveal it.
#[verifier::opaque]
pub open spec fn iommu_table_tlb_entries_present(iommu_tlb: IommuTLB, root_table: IommuRootTable, iommu_table_map: IommuTableLockedMap, it: RwLockPageTableRoot) -> bool {
    iommu_table_map.spec_index(it).view().did matches Some(did) ==> single_tlb_subset_of_present_pagetable(iommu_tlb.spec_index(did), iommu_table_map.spec_index(it).view())
}
}
