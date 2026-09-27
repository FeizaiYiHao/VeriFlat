use vstd::prelude::*;
use crate::*;

verus! {
pub ghost struct IommuRootTableU {
    pub owners: Seq3<RwLockProcessPtr>,
    pub iommu_roots: Seq3<Option<PageTableRoot>>,
}

impl IommuRootTable {
    #[verifier::opaque]
    pub open spec fn user_view(&self) -> IommuRootTableU {
        IommuRootTableU { owners: self.owners(), iommu_roots: self.iommu_roots() }
    }
}
}
