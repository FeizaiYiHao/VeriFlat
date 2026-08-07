use vstd::prelude::*;

verus! {

use crate::*;

pub open spec fn spec_iotlb_entry_equal_to_map_entry(
    iotlb_entry: TLBEntry,
    map_entry: MapEntry,
) -> bool {
    &&& iotlb_entry.addr == map_entry.addr
    &&& iotlb_entry.execute_disable == map_entry.execute_disable
    &&& iotlb_entry.write == map_entry.write
}

/// Every cached translation for one DID remains backed by the same kernel IOMMU
/// page-table mapping. The hardware present bit may already be clear while an
/// old IOTLB entry awaits invalidation; this invariant does not encode that
/// state through the page-table lock.
pub open spec fn single_iotlb_subset_of_iommu_table(
    iotlb: SingleIotlb,
    iommu_table: PageTable<IOMMU_TYPE>,
) -> bool {
    &&& forall|iova: Iova|
        #![trigger iommu_table.mapping_4k().dom().contains(iova)]
        #![trigger iotlb.entries_4k().spec_index(iova)]
        iotlb.entries_4k().dom().contains(iova)
        ==>
        iommu_table.mapping_4k().dom().contains(iova)
        && spec_iotlb_entry_equal_to_map_entry(
            iotlb.entries_4k().spec_index(iova),
            iommu_table.mapping_4k().spec_index(iova),
        )
    &&& forall|iova: Iova|
        #![trigger iommu_table.mapping_2m().dom().contains(iova)]
        #![trigger iotlb.entries_2m().spec_index(iova)]
        iotlb.entries_2m().dom().contains(iova)
        ==>
        iommu_table.mapping_2m().dom().contains(iova)
        && spec_iotlb_entry_equal_to_map_entry(
            iotlb.entries_2m().spec_index(iova),
            iommu_table.mapping_2m().spec_index(iova),
        )
    &&& forall|iova: Iova|
        #![trigger iommu_table.mapping_1g().dom().contains(iova)]
        #![trigger iotlb.entries_1g().spec_index(iova)]
        iotlb.entries_1g().dom().contains(iova)
        ==>
        iommu_table.mapping_1g().dom().contains(iova)
        && spec_iotlb_entry_equal_to_map_entry(
            iotlb.entries_1g().spec_index(iova),
            iommu_table.mapping_1g().spec_index(iova),
        )
}

/// The global IOTLB is indexed by DID.  In the current identity model DID is
/// the 16-bit BDF encoding, so the static root table selects the unique owner
/// and the owner's one IOMMU table without a CPU dirty bitmap.
#[verifier::opaque]
pub open spec fn iommu_tlb_wf_spec(
    iommu_tlb: IommuTLB,
    root_table: &IommuRootTable,
    process_map: ProcessLockedMap,
    iommu_table_map: IommuTableLockedMap,
) -> bool {
    &&& iommu_tlb.inv()
    &&& root_table.wf()
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        #![trigger root_table.spec_index_iommu_root(bus, device, function)]
        #![trigger iommu_tlb.spec_index(pci_bdf_did(bus, device, function))]
        pci_bdf_valid(bus, device, function)
        ==> {
            let did = pci_bdf_did(bus, device, function);
            let domain_tlb = iommu_tlb.spec_index(did);
            let proc_ptr = root_table.spec_index_owner(bus, device, function);
            let iommu_root = root_table.spec_index_iommu_root(bus, device, function);
            &&& vtd_domain_id_valid(did)
            &&& process_map.dom().contains(proc_ptr)
            &&& iommu_root is None ==> domain_tlb.is_empty()
            &&& iommu_root is Some ==> {
                &&& process_map.spec_index(proc_ptr).view().iommu_table is Some
                &&& {
                    let iommu_table =
                        process_map.spec_index(proc_ptr).view().iommu_table.unwrap();
                    &&& iommu_table_map.dom().contains(iommu_table)
                    &&& iommu_table_map.spec_index(iommu_table).view().proc_ptr
                        == proc_ptr
                    &&& iommu_root.unwrap()
                        == iommu_table_map.spec_index(iommu_table).view().cr3
                    &&& single_iotlb_subset_of_iommu_table(
                        domain_tlb,
                        iommu_table_map.spec_index(iommu_table).view(),
                    )
                }
            }
        }
}

}
