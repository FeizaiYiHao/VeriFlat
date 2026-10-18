use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn iommu_table_perms_wf(iommu_table_map: IommuTableLockedMap) -> bool {
    &&& iommu_table_map.perms_wf()
    &&& pagetables_inv(iommu_table_map)
    &&& iommu_table_hidden_leaves_only_when_wlocked(iommu_table_map)
}

/// An IOMMU table with a leaf the device cannot see is write-locked: thread exit clears present bits and reclaims
/// those leaves before it releases the table.
#[verifier::opaque]
pub open spec fn iommu_table_hidden_leaves_only_when_wlocked(iommu_table_map: IommuTableLockedMap) -> bool {
    forall|iommu_table: RwLockPageTableRoot|
        #![trigger iommu_table_map.spec_index(iommu_table).locking_thread()]
        iommu_table_map.dom().contains(iommu_table) && !iommu_table_map.spec_index(iommu_table).view().leaves_present() ==> iommu_table_map.spec_index(iommu_table).locking_thread() is Write
}

pub proof fn iommu_table_perms_wf_at(iommu_table_map: IommuTableLockedMap, iommu_table_ptr: RwLockPageTableRoot)
    requires
        iommu_table_perms_wf(iommu_table_map),
        iommu_table_map.dom().contains(iommu_table_ptr),
    ensures
        iommu_table_map.view().spec_index(iommu_table_ptr).is_init(),
        iommu_table_map.view().spec_index(iommu_table_ptr).addr() == iommu_table_ptr,
        iommu_table_map.spec_index(iommu_table_ptr).inv(),
        iommu_table_map.spec_index(iommu_table_ptr).is_init(),
        iommu_table_map.spec_index(iommu_table_ptr).view().inv(),
{ reveal(iommu_table_perms_wf); }

pub proof fn iommu_table_perms_wf_map(iommu_table_map: IommuTableLockedMap)
    requires iommu_table_perms_wf(iommu_table_map)
    ensures iommu_table_map.perms_wf()
{ reveal(iommu_table_perms_wf); }
}
