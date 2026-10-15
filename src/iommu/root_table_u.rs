use vstd::prelude::*;
use crate::*;

verus! {
/// The user view names owners and whether DMA translation is attached; the
/// physical second-level root behind a present context entry stays in K.
pub ghost struct IommuRootTableU {
    pub owners: Seq3<RwLockProcessPtr>,
    pub attached: Seq3<bool>,
}

pub open spec fn iommu_roots_attached(iommu_roots: Seq3<Option<PageTableRoot>>) -> Seq3<bool> {
    Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int|
        Seq::new(PCI_FUNCTION_COUNT as nat, |function: int| iommu_roots[bus][device][function] is Some)))
}

impl IommuRootTable {
    #[verifier::opaque]
    pub open spec fn user_view(&self) -> IommuRootTableU { IommuRootTableU { owners: self.owners(), attached: iommu_roots_attached(self.iommu_roots()) } }

    pub proof fn user_view_unfold(&self)
        ensures self.user_view() == (IommuRootTableU { owners: self.owners(), attached: iommu_roots_attached(self.iommu_roots()) }),
    { reveal(IommuRootTable::user_view); }
}
}
