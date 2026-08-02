use vstd::prelude::*;
use crate::*;

verus! {

#[verifier::opaque]
pub open spec fn iommu_table_perms_wf(
    iommu_table_map: IommuTableLockedMap,
) -> bool {
    &&& iommu_table_map.perms_wf()
    &&& forall|iommu_root: RwLockPageTableRoot|
        #![trigger iommu_table_map.spec_index(iommu_root).view().inv()]
        iommu_table_map.dom().contains(iommu_root)
        ==> iommu_table_map.spec_index(iommu_root).view().inv()
}

}
