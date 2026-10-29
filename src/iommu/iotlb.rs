use vstd::prelude::*;

// Platform implementation: on every remapping unit, a domain-selective context-cache
// invalidation followed by a domain-selective IOTLB invalidation for `did`, each awaited.
unsafe extern "C" {
    fn veriflat_iommu_invalidate_domain(did: usize);
    // Domain-selective IOTLB invalidation for `did` on every unit, awaited; the context cache is untouched.
    fn veriflat_iommu_invalidate_iotlb_domain(did: usize);
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
/// A context-cache key means a unit may cache that BDF's context entry; its value is the entry's second-level root and DID (`CAP.CM = 0`: not-present entries are never cached).
/// The ATS/device-TLB is not state: every present context entry has translation type 0 (see `IommuRootTable::wf`).
pub struct IommuTLB {
    pub domain_tlbs: Ghost<Map<VtdDomainId, SingleTLB>>,
    pub context_cache: Ghost<Map<PciBdf, (PageTableRoot, VtdDomainId)>>,
}

impl IommuTLB {
    pub fn new_empty() -> (ret: Self)
        ensures
            ret.inv(),
            forall|did: VtdDomainId| #![trigger ret.spec_index(did)] vtd_domain_id_valid(did) ==> ret.spec_index(did).is_empty(),
            ret.context_cache() == Map::<PciBdf, (PageTableRoot, VtdDomainId)>::empty(),
    {
        let ghost domain_ids = Set::range(0usize, VTD_DOMAIN_COUNT);
        let ret = Self { domain_tlbs: Ghost(Map::new(domain_ids, |_did: VtdDomainId| SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })), context_cache: Ghost(Map::empty()) };
        assert(ret.inv()) by { reveal(IommuTLB::inv); }
        ret
    }

    /// Drops every cached context entry tagged `did`, then empties its IOTLB domain, in the order VT-d requires.
    /// The root-table lock serializes it with the context-entry update that makes it necessary. The unit may refill the
    /// domain and the context entries tagged `did` at once with what `k`, the kernel state whose IOTLB this is, presents.
    #[verifier::external_body]
    pub fn invalidate_domain(&mut self, did: VtdDomainId, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            k.iommu_tlb == *old(self),
            vtd_domain_id_valid(did),
            !lctx.iommu_root_table_lock_map().dom().is_empty(),
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert(did, final(self).spec_index(did)),
            iommu_tlb_within_may_cache(k, did, final(self).spec_index(did)),
            Map::new(final(self).context_cache().dom().filter(|bdf: PciBdf| final(self).context_cache()[bdf].1 != did), |bdf: PciBdf| final(self).context_cache()[bdf])
                == Map::new(old(self).context_cache().dom().filter(|bdf: PciBdf| old(self).context_cache()[bdf].1 != did), |bdf: PciBdf| old(self).context_cache()[bdf]),
            forall|bdf: PciBdf| #![trigger final(self).context_cache().dom().contains(bdf)] final(self).context_cache().dom().contains(bdf) && final(self).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(k, bdf, final(self).context_cache()[bdf]),
    {
        unsafe { veriflat_iommu_invalidate_domain(did); }
        self.domain_tlbs = Ghost(self.domain_tlbs.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
        self.context_cache = Ghost(Map::new(self.context_cache.view().dom().filter(|bdf: PciBdf| self.context_cache.view()[bdf].1 != did), |bdf: PciBdf| self.context_cache.view()[bdf]));
    }

    /// Empties only the DID's IOTLB domain; the context cache is untouched. The unit may refill the domain at once with
    /// what `k`, the kernel state whose IOTLB this is, presents.
    /// A held IOMMU-table lock serializes it with the leaf update that makes it necessary.
    #[verifier::external_body]
    pub fn invalidate_iotlb_domain(&mut self, did: VtdDomainId, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            k.iommu_tlb == *old(self),
            vtd_domain_id_valid(did),
            !lctx.iommu_table_lock_map().dom().is_empty(),
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert(did, final(self).spec_index(did)),
            iommu_tlb_within_may_cache(k, did, final(self).spec_index(did)),
            final(self).context_cache() == old(self).context_cache(),
    {
        unsafe { veriflat_iommu_invalidate_iotlb_domain(did); }
        self.domain_tlbs = Ghost(self.domain_tlbs.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
    }

    pub open spec fn view(&self) -> Map<VtdDomainId, SingleTLB> { self.domain_tlbs.view() }

    pub open spec fn context_cache(&self) -> Map<PciBdf, (PageTableRoot, VtdDomainId)> { self.context_cache.view() }

    pub open spec fn spec_index(&self, did: VtdDomainId) -> SingleTLB
        recommends
            self.inv(),
            vtd_domain_id_valid(did),
    {
        self.view().spec_index(did)
    }

    #[verifier::opaque]
    pub open spec fn inv(&self) -> bool {
        &&& forall|did: VtdDomainId| #![trigger self.view().dom().contains(did)] self.view().dom().contains(did) <==> vtd_domain_id_valid(did)
        &&& forall|bdf: PciBdf| #![trigger self.context_cache().dom().contains(bdf)]
            self.context_cache().dom().contains(bdf) ==> pci_bdf_valid(bdf.0, bdf.1, bdf.2) && vtd_domain_id_valid(self.context_cache()[bdf].1)
    }
}
}
