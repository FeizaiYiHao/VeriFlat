use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn iommu_table_perms_wf(iommu_table_map: IommuTableLockedMap) -> bool {
    &&& iommu_table_map.perms_wf()
    &&& pagetables_inv(iommu_table_map)
}
}
