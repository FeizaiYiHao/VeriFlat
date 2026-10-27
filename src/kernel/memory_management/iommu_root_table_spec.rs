use vstd::prelude::*;

verus! {
use crate::*;

/// Connects the root table's two logical interfaces to the process map and to
/// each present second-stage IOMMU page-table root.  Ownership is total even
/// when translation is disabled (`iommu_root is None`).  Every present context
/// entry carries its owner table's root and `Some` DID, so a table whose `did`
/// is `None` has no attached function and all attached functions of a table
/// share its DID.  A table DID `d` is anchored at the B/D/F `pci_bdf_of_did(d)`:
/// owned by the table's process, attached to the table, and carrying `d`.
#[verifier::opaque]
pub open spec fn iommu_root_table_process_wf(root_table: IommuRootTable, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap) -> bool {
    &&& root_table.wf()
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        #![trigger root_table.spec_index_iommu_root(bus, device, function)]
        pci_bdf_valid(bus, device, function) ==> {
            let proc_ptr = root_table.spec_index_owner(bus, device, function);
            let iommu_root = root_table.spec_index_iommu_root(bus, device, function);
            &&& process_map.dom().contains(proc_ptr)
            &&& iommu_root is Some ==> {
                &&& process_map.spec_index(proc_ptr).view().iommu_table is Some
                &&& {
                    let iommu_table = process_map.spec_index(proc_ptr).view().iommu_table.unwrap();
                    &&& iommu_table_map.dom().contains(iommu_table)
                    &&& iommu_table_map.spec_index(iommu_table).view().proc_ptr == proc_ptr
                    &&& iommu_root.unwrap() == iommu_table_map.spec_index(iommu_table).view().cr3
                    &&& iommu_table_map.spec_index(iommu_table).view().did is Some
                    &&& root_table.spec_index_iommu_did(bus, device, function) == iommu_table_map.spec_index(iommu_table).view().did
                }
            }
        }
    &&& forall|it: RwLockPageTableRoot|
        #![trigger iommu_table_map.spec_index(it).view().did]
        iommu_table_map.dom().contains(it) && iommu_table_map.spec_index(it).view().did is Some ==> {
            let table = iommu_table_map.spec_index(it).view();
            let did = table.did->Some_0;
            let anchor = pci_bdf_of_did(did);
            &&& vtd_domain_id_valid(did)
            &&& root_table.spec_index_owner(anchor.0, anchor.1, anchor.2) == table.proc_ptr
            &&& root_table.spec_index_iommu_root(anchor.0, anchor.1, anchor.2) == Some(table.cr3)
            &&& root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did)
        }
}

/// The DID anchoring of `iommu_root_table_process_wf` at the IOMMU table `it`.
pub proof fn iommu_root_table_process_wf_table_at(root_table: IommuRootTable, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap, it: RwLockPageTableRoot)
    requires
        iommu_root_table_process_wf(root_table, process_map, iommu_table_map),
        iommu_table_map.dom().contains(it),
    ensures
        iommu_table_map.spec_index(it).view().did is Some ==> {
            let table = iommu_table_map.spec_index(it).view();
            let did = table.did->Some_0;
            let anchor = pci_bdf_of_did(did);
            &&& vtd_domain_id_valid(did)
            &&& root_table.spec_index_owner(anchor.0, anchor.1, anchor.2) == table.proc_ptr
            &&& root_table.spec_index_iommu_root(anchor.0, anchor.1, anchor.2) == Some(table.cr3)
            &&& root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did)
        },
{ reveal(iommu_root_table_process_wf); }
}
