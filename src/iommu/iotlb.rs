use vstd::prelude::*;

// Platform implementation: queue a domain-selective IOTLB invalidation for the
// VT-d domain `did` on the remapping unit and wait for its completion.
unsafe extern "C" {
    fn veriflat_iommu_invalidate_domain(did: usize);
}

verus! {
use crate::*;

pub type VtdDomainId = usize;

/// The current kernel model has one VT-d remapping unit and therefore one
/// global IOTLB.  Generalizing this becomes an array indexed by unit id.
pub const VTD_DOMAIN_COUNT: usize = 65_536;

pub open spec fn vtd_domain_id_valid(did: VtdDomainId) -> bool { did < VTD_DOMAIN_COUNT }

/// One logical IOTLB for the single VT-d remapping unit currently modeled by
/// VeriFlat.  Entries are tagged by DID, not by CPU; each domain reuses the CPU
/// `SingleTLB` shape keyed by IOVA.  The VT-d context cache and endpoint
/// ATS/device-TLB caches are intentionally separate future state.
pub struct IommuTLB {
    pub domain_tlbs: Ghost<Map<VtdDomainId, SingleTLB>>,
}

impl IommuTLB {
    pub fn new_empty() -> (ret: Self)
        ensures
            ret.inv(),
            forall|did: VtdDomainId|
                #![trigger ret.spec_index(did)]
                vtd_domain_id_valid(did) ==> ret.spec_index(did).is_empty(),
    {
        let ghost domain_ids = Set::range(0usize, VTD_DOMAIN_COUNT);
        let ret = Self { domain_tlbs: Ghost(Map::new(domain_ids, |_did: VtdDomainId| SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })) };
        assert(ret.inv()) by { reveal(IommuTLB::inv); }
        ret
    }

    /// Domain-selective invalidation; the root-table lock serializes it with
    /// the context-entry update that makes it necessary.
    #[verifier::external_body]
    pub fn invalidate_domain(&mut self, did: VtdDomainId, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            vtd_domain_id_valid(did),
            !lctx.iommu_root_table_lock_map().dom().is_empty(),
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
    {
        unsafe { veriflat_iommu_invalidate_domain(did); }
        self.domain_tlbs = Ghost(self.domain_tlbs.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
    }

    pub open spec fn view(&self) -> Map<VtdDomainId, SingleTLB> { self.domain_tlbs.view() }

    pub open spec fn spec_index(&self, did: VtdDomainId) -> SingleTLB
        recommends
            self.inv(),
            vtd_domain_id_valid(did),
    {
        self.view().spec_index(did)
    }

    #[verifier::opaque]
    pub open spec fn inv(&self) -> bool {
        forall|did: VtdDomainId|
            #![trigger self.view().dom().contains(did)]
            self.view().dom().contains(did) <==> vtd_domain_id_valid(did)
    }
}
}
