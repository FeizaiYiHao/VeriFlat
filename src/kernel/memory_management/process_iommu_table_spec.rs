use vstd::prelude::*;
use crate::*;

verus! {

#[verifier::opaque]
pub open spec fn process_iommu_table_match(
    process_map: ProcessLockedMap,
    iommu_table_map: IommuTableLockedMap,
) -> bool {
    // Process -> IOMMU table.
    &&& forall|proc_ptr: RwLockProcessPtr|
        #![trigger process_map.spec_index(proc_ptr).view().iommu_table]
        process_map.dom().contains(proc_ptr)
        && process_map.spec_index(proc_ptr).view().iommu_table is Some
        ==>
        {
            let iommu_root =
                process_map.spec_index(proc_ptr).view().iommu_table.unwrap();
            &&& iommu_table_map.dom().contains(iommu_root)
            &&& iommu_table_map.spec_index(iommu_root).view().proc_ptr == proc_ptr
        }
    // IOMMU table -> process.
    &&& forall|iommu_root: RwLockPageTableRoot|
        #![trigger iommu_table_map.spec_index(iommu_root).view().proc_ptr]
        iommu_table_map.dom().contains(iommu_root)
        ==>
        {
            let proc_ptr = iommu_table_map.spec_index(iommu_root).view().proc_ptr;
            &&& process_map.dom().contains(proc_ptr)
            &&& process_map.spec_index(proc_ptr).view().iommu_table
                == Some(iommu_root)
        }
}

}
