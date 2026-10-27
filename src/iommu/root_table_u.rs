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

/// The DID of `owner`'s IOMMU table, `old_did` before and `new_did` after `bdf` is detached and handed away, under the
/// owner slots `owners` and attached flags `attached` before the hand-off. Handing away the attached anchor of the table
/// (`old_did == Some(pci_bdf_did(bdf))`) re-anchors it at the candidate DID of the lexicographically first remaining
/// attached B/D/F of `owner`, or leaves it without a DID when none remains; any other hand-off keeps `old_did`.
pub open spec fn pci_handoff_table_did(
    owners: Seq3<RwLockProcessPtr>, attached: Seq3<bool>, owner: RwLockProcessPtr, bdf: PciBdf, old_did: Option<VtdDomainId>, new_did: Option<VtdDomainId>,
) -> bool {
    if attached[bdf.0 as int][bdf.1 as int][bdf.2 as int] && old_did == Some(pci_bdf_did(bdf.0, bdf.1, bdf.2)) {
        &&& new_did matches Some(did) ==> {
            let anchor = pci_bdf_of_did(did);
            &&& vtd_domain_id_valid(did)
            &&& anchor != bdf
            &&& owners[anchor.0 as int][anchor.1 as int][anchor.2 as int] == owner
            &&& attached[anchor.0 as int][anchor.1 as int][anchor.2 as int]
        }
        &&& forall|b: usize, d: usize, f: usize| #![trigger owners[b as int][d as int][f as int]] #![trigger attached[b as int][d as int][f as int]]
            pci_bdf_valid(b, d, f) && (b, d, f) != bdf && owners[b as int][d as int][f as int] == owner && attached[b as int][d as int][f as int]
                ==> new_did is Some && !pci_bdf_lt((b, d, f), pci_bdf_of_did(new_did->Some_0))
    } else { new_did == old_did }
}

impl IommuRootTable {
    #[verifier::opaque]
    pub open spec fn user_view(&self) -> IommuRootTableU { IommuRootTableU { owners: self.owners(), attached: iommu_roots_attached(self.iommu_roots()) } }

    pub proof fn user_view_unfold(&self)
        ensures self.user_view() == (IommuRootTableU { owners: self.owners(), attached: iommu_roots_attached(self.iommu_roots()) }),
    { reveal(IommuRootTable::user_view); }
}
}
