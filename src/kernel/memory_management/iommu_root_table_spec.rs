use vstd::prelude::*;

verus! {

use crate::*;

/// Connects the root table's two logical interfaces to the process map and to
/// each present second-stage IOMMU page-table root.  Ownership is total even
/// when translation is disabled (`iommu_root is None`).
#[verifier::opaque]
pub open spec fn iommu_root_table_process_wf(
    root_table: &IommuRootTable,
    process_map: ProcessLockedMap,
    iommu_table_map: IommuTableLockedMap,
) -> bool {
    &&& root_table.wf()
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        #![trigger root_table.spec_index_iommu_root(bus, device, function)]
        pci_bdf_valid(bus, device, function)
        ==> {
            let proc_ptr = root_table.spec_index_owner(bus, device, function);
            let iommu_root = root_table.spec_index_iommu_root(bus, device, function);
            &&& process_map.dom().contains(proc_ptr)
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
                }
            }
        }
}

}
