use vstd::prelude::*;

verus! {
use crate::*;

/// The global IOTLB is indexed by DID.  In the current identity model DID is
/// the 16-bit BDF encoding, so the static root table selects the unique owner
/// and the owner's one IOMMU table without a CPU dirty bitmap.  Ownership and
/// root/table agreement live in `iommu_root_table_process_wf`; this predicate
/// only constrains the cached translations.  The hardware present bit may
/// already be clear while an old IOTLB entry awaits invalidation.
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
            &&& vtd_domain_id_valid(did)
            &&& iommu_root is None ==> domain_tlb.is_empty()
            &&& iommu_root is Some ==> single_tlb_subset_of_pagetable(domain_tlb, iommu_table_map.spec_index(process_map.spec_index(proc_ptr).view().iommu_table.unwrap()).view())
        }
}
}
