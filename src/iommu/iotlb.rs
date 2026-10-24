use vstd::prelude::*;

// Platform implementation: on every remapping unit, a domain-selective context-cache
// invalidation followed by a domain-selective IOTLB invalidation for `did`, each awaited.
unsafe extern "C" {
    fn veriflat_iommu_invalidate_domain(did: usize);
    // Global IOTLB invalidation on every unit, awaited; the platform serializes register access with its own spinlock.
    fn veriflat_iommu_flush_all_iotlb();
}

verus! {
use crate::*;

pub type VtdDomainId = usize;

/// The current kernel model has one VT-d remapping unit and therefore one
/// global IOTLB.  Generalizing this becomes an array indexed by unit id.
pub const VTD_DOMAIN_COUNT: usize = 65_536;

pub open spec fn vtd_domain_id_valid(did: VtdDomainId) -> bool { did < VTD_DOMAIN_COUNT }

/// One logical IOTLB and one logical context cache for all remapping units: they share the one root table, and the hook invalidates every unit.
/// IOTLB entries are tagged by DID; each domain reuses the CPU `SingleTLB` shape keyed by IOVA.
/// A context-cache key means a unit may cache that DID's context entry; its value is the entry's second-level root (`CAP.CM = 0`: not-present entries are never cached).
/// The ATS/device-TLB is not state: every present context entry has translation type 0 (see `IommuRootTable::wf`).
pub struct IommuTLB {
    pub domain_tlbs: Ghost<Map<VtdDomainId, SingleTLB>>,
    pub context_cache: Ghost<Map<VtdDomainId, PageTableRoot>>,
}

impl IommuTLB {
    pub fn new_empty() -> (ret: Self)
        ensures
            ret.inv(),
            forall|did: VtdDomainId|
                #![trigger ret.spec_index(did)]
                vtd_domain_id_valid(did) ==> ret.spec_index(did).is_empty(),
            ret.context_cache() == Map::<VtdDomainId, PageTableRoot>::empty(),
    {
        let ghost domain_ids = Set::range(0usize, VTD_DOMAIN_COUNT);
        let ret = Self { domain_tlbs: Ghost(Map::new(domain_ids, |_did: VtdDomainId| SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })), context_cache: Ghost(Map::empty()) };
        assert(ret.inv()) by { reveal(IommuTLB::inv); }
        ret
    }

    /// Drops the DID's cached context entry, then empties its IOTLB domain, in the order VT-d requires.
    /// The root-table lock serializes it with the context-entry update that makes it necessary.
    #[verifier::external_body]
    pub fn invalidate_domain(&mut self, did: VtdDomainId, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            vtd_domain_id_valid(did),
            !lctx.iommu_root_table_lock_map().dom().is_empty(),
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
            final(self).context_cache() == old(self).context_cache().remove(did),
    {
        unsafe { veriflat_iommu_invalidate_domain(did); }
        self.domain_tlbs = Ghost(self.domain_tlbs.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
        self.context_cache = Ghost(self.context_cache.view().remove(did));
    }

    /// Empties every IOTLB domain; the context cache is untouched. Needs no kernel lock: the platform serializes the registers.
    #[verifier::external_body]
    pub fn flush_all_iotlb(&mut self)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).view().dom() == old(self).view().dom(),
            forall|did: VtdDomainId| #![trigger final(self).spec_index(did)] vtd_domain_id_valid(did) ==> final(self).spec_index(did).is_empty(),
            final(self).context_cache() == old(self).context_cache(),
    {
        unsafe { veriflat_iommu_flush_all_iotlb(); }
        self.domain_tlbs = Ghost(Map::new(self.domain_tlbs.view().dom(), |_did: VtdDomainId| SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
    }

    pub open spec fn view(&self) -> Map<VtdDomainId, SingleTLB> { self.domain_tlbs.view() }

    pub open spec fn context_cache(&self) -> Map<VtdDomainId, PageTableRoot> { self.context_cache.view() }

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
