use vstd::prelude::*;
use crate::*;
verus! {
/// An attached function's IOMMU table is never write-locked, so a device never sees a hidden leaf, and a write-locked
/// IOMMU table is held by the thread that write-holds its process, so attach (holding the process) can rely on it.
// Proof dependency (confirmed): process_iommu_table_match.
#[verifier::opaque]
pub open spec fn iommu_table_lock_wf(root_table: IommuRootTable, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap) -> bool {
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_iommu_root(bus, device, function)]
        pci_bdf_valid(bus, device, function) && root_table.spec_index_iommu_root(bus, device, function) is Some ==> {
            let proc_ptr = root_table.spec_index_owner(bus, device, function);
            &&& process_map.dom().contains(proc_ptr)
            &&& process_map.spec_index(proc_ptr).view().iommu_table is Some
            &&& iommu_table_map.dom().contains(process_map.spec_index(proc_ptr).view().iommu_table.unwrap())
            &&& !(iommu_table_map.spec_index(process_map.spec_index(proc_ptr).view().iommu_table.unwrap()).locking_thread() is Write)
        }
    &&& forall|iommu_table: RwLockPageTableRoot|
        #![trigger iommu_table_map.spec_index(iommu_table).locking_thread()]
        iommu_table_map.dom().contains(iommu_table) && iommu_table_map.spec_index(iommu_table).locking_thread() is Write ==> {
            let proc_ptr = iommu_table_map.spec_index(iommu_table).view().proc_ptr;
            &&& process_map.dom().contains(proc_ptr)
            &&& process_map.spec_index(proc_ptr).locking_thread() is Write
            &&& process_map.spec_index(proc_ptr).locking_thread()->Write_thread_id == iommu_table_map.spec_index(iommu_table).locking_thread()->Write_thread_id
        }
}
}
