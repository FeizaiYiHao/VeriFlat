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
pub open spec fn iommu_root_table_process_wf(irt: IommuRootTable, prc_mp: ProcessLockedMap, it_mp: IommuTableLockedMap) -> bool {
    &&& irt.wf()
    // Each B/D/F is owned by a process; a present context entry names that process's IOMMU table, its root, and its DID.
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger irt.spec_index_owner(bus, device, function)]
        #![trigger irt.spec_index_iommu_root(bus, device, function)]
        pci_bdf_valid(bus, device, function) ==> {
            let prc_ptr = irt.spec_index_owner(bus, device, function);
            let iommu_root = irt.spec_index_iommu_root(bus, device, function);
            let it_ptr = prc_mp.spec_index(prc_ptr).view().iommu_table->Some_0;
            &&& prc_mp.dom().contains(prc_ptr)
            &&& iommu_root is Some ==> {
                &&& prc_mp.spec_index(prc_ptr).view().iommu_table is Some
                &&& it_mp.dom().contains(it_ptr)
                &&& it_mp.spec_index(it_ptr).view().proc_ptr == prc_ptr
                &&& iommu_root.unwrap() == it_mp.spec_index(it_ptr).view().cr3
                &&& it_mp.spec_index(it_ptr).view().did is Some
                &&& irt.spec_index_iommu_did(bus, device, function) == it_mp.spec_index(it_ptr).view().did
            }
        }
    // A table's DID is anchored at the B/D/F `pci_bdf_of_did(did)`.
    &&& forall|it: RwLockPageTableRoot|
        #![trigger it_mp.spec_index(it).view().did]
        it_mp.dom().contains(it) && it_mp.spec_index(it).view().did is Some ==> {
            let table = it_mp.spec_index(it).view();
            let did = table.did->Some_0;
            let anchor = pci_bdf_of_did(did);
            &&& vtd_domain_id_valid(did)
            &&& irt.spec_index_owner(anchor.0, anchor.1, anchor.2) == table.proc_ptr
            &&& irt.spec_index_iommu_root(anchor.0, anchor.1, anchor.2) == Some(table.cr3)
            &&& irt.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did)
        }
}

/// The DID anchoring of `iommu_root_table_process_wf` at the IOMMU table `it_ptr`.
pub proof fn iommu_root_table_process_wf_table_at(irt: IommuRootTable, prc_mp: ProcessLockedMap, it_mp: IommuTableLockedMap, it_ptr: RwLockPageTableRoot)
    requires
        iommu_root_table_process_wf(irt, prc_mp, it_mp),
        it_mp.dom().contains(it_ptr),
    ensures
        it_mp.spec_index(it_ptr).view().did is Some ==> {
            let table = it_mp.spec_index(it_ptr).view();
            let did = table.did->Some_0;
            let anchor = pci_bdf_of_did(did);
            &&& vtd_domain_id_valid(did)
            &&& irt.spec_index_owner(anchor.0, anchor.1, anchor.2) == table.proc_ptr
            &&& irt.spec_index_iommu_root(anchor.0, anchor.1, anchor.2) == Some(table.cr3)
            &&& irt.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did)
        },
{ reveal(iommu_root_table_process_wf); }
}
