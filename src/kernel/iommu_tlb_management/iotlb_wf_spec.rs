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

/// Every cached translation for one DID remains backed by the same IOMMU
/// page-table mapping.  While the table is write-locked, software may have
/// cleared the hardware present bit in preparation for invalidation, but it
/// must retain the mapping and physical address until the IOTLB entry is gone.
pub open spec fn single_iotlb_subset_of_iommu_table(
    iotlb: SingleIotlb,
    iommu_table: RwLock<
        PageTable<IOMMU_TYPE>,
        (),
        (),
        (),
        PAGE_TABLE_HAS_KILL_STATE,
    >,
) -> bool {
    &&& forall|iova: Iova|
        #![trigger iommu_table.view().mapping_4k().dom().contains(iova)]
        #![trigger iotlb.entries_4k().spec_index(iova)]
        iotlb.entries_4k().dom().contains(iova)
        ==>
        iova_4k_valid(iova)
        && iommu_table.view().mapping_4k().dom().contains(iova)
        && (iommu_table.wlocked() == false
            ==> iommu_table.view().mapping_4k().spec_index(iova).present)
        && spec_iotlb_entry_equal_to_map_entry(
            iotlb.entries_4k().spec_index(iova),
            iommu_table.view().mapping_4k().spec_index(iova),
        )
    &&& forall|iova: Iova|
        #![trigger iommu_table.view().mapping_2m().dom().contains(iova)]
        #![trigger iotlb.entries_2m().spec_index(iova)]
        iotlb.entries_2m().dom().contains(iova)
        ==>
        iova_2m_valid(iova)
        && iommu_table.view().mapping_2m().dom().contains(iova)
        && (iommu_table.wlocked() == false
            ==> iommu_table.view().mapping_2m().spec_index(iova).present)
        && spec_iotlb_entry_equal_to_map_entry(
            iotlb.entries_2m().spec_index(iova),
            iommu_table.view().mapping_2m().spec_index(iova),
        )
    &&& forall|iova: Iova|
        #![trigger iommu_table.view().mapping_1g().dom().contains(iova)]
        #![trigger iotlb.entries_1g().spec_index(iova)]
        iotlb.entries_1g().dom().contains(iova)
        ==>
        iova_1g_valid(iova)
        && iommu_table.view().mapping_1g().dom().contains(iova)
        && (iommu_table.wlocked() == false
            ==> iommu_table.view().mapping_1g().spec_index(iova).present)
        && spec_iotlb_entry_equal_to_map_entry(
            iotlb.entries_1g().spec_index(iova),
            iommu_table.view().mapping_1g().spec_index(iova),
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
                        iommu_table_map.spec_index(iommu_table),
                    )
                }
            }
        }
}

}
