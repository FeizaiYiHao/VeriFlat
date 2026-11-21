use vstd::prelude::*;

// Platform implementation: on every remapping unit, a domain-selective context-cache
// invalidation followed by a domain-selective IOTLB invalidation for `did`, each awaited.
unsafe extern "C" {
    fn veriflat_iommu_invalidate_domain(did: usize);
    // Domain-selective IOTLB invalidation for `did` on every unit, awaited; the context cache is untouched.
    fn veriflat_iommu_invalidate_iotlb_domain(did: usize);
    // Writes the cache lines overlapping [addr, addr + len) back to memory when some unit does not snoop CPU caches
    // (ECAP.C = 0), so the unit reads what the kernel stored; otherwise does nothing.
    pub(crate) fn veriflat_iommu_flush_to_memory(addr: usize, len: usize);
}

verus! {
use crate::*;

pub type VtdDomainId = usize;

/// Number of VT-d domain IDs (16-bit DID).
pub const VTD_DOMAIN_COUNT: usize = 65_536;

pub open spec fn vtd_domain_id_valid(did: VtdDomainId) -> bool { did < VTD_DOMAIN_COUNT }

/// One logical IOTLB, one logical context cache, and one logical set of paging-structure caches for all remapping units:
/// they share the one root table, and the hooks invalidate every unit.
/// IOTLB entries are tagged by DID; each domain reuses the CPU `SingleTLB` shape keyed by IOVA.
/// A context-cache key means a unit may cache that BDF's context entry; its value is the entry's second-level root and DID (`CAP.CM = 0`: not-present entries are never cached).
/// The second-stage paging-structure caches are tagged by DID and address (VT-d 5.20, 6.2.1 Table 17, legacy mode); each
/// domain reuses the CPU `PagingStructureCache` shape: an L4, L3, or L2 index path names the next table page. With
/// `CAP.CM = 0` they hold only entries of successful walks (6.2.5.5). K only.
/// The ATS/device-TLB is not state: every present context entry has translation type 0 (see `IommuRootTable::wf`).
/// Managed table well-formedness excludes W-only entries, making the present/R refill abstraction valid.
/// Sealed hardware state: only the invalidation primitives below write it, and only the boot glue constructs it.
pub struct IommuTLB {
    domain_tlbs: Ghost<Map<VtdDomainId, SingleTLB>>,
    context_cache: Ghost<Map<PciBdf, (PageTableRoot, VtdDomainId)>>,
    structure_caches: Ghost<Map<VtdDomainId, PagingStructureCache>>,
}

impl IommuTLB {
    /// Callable only from the unverified boot glue; `requires false` keeps verified code out.
    pub fn new_empty() -> (ret: Self)
        requires false,
        ensures
            ret.inv(),
            forall|did: VtdDomainId| #![trigger ret.spec_index(did)] vtd_domain_id_valid(did) ==> ret.spec_index(did).is_empty(),
            ret.context_cache() == Map::<PciBdf, (PageTableRoot, VtdDomainId)>::empty(),
            forall|did: VtdDomainId| #![trigger ret.structure_cache(did)] vtd_domain_id_valid(did) ==> ret.structure_cache(did).is_empty(),
    {
        let ghost domain_ids = Set::range(0usize, VTD_DOMAIN_COUNT);
        let ret = Self {
            domain_tlbs: Ghost(Map::new(domain_ids, |_did: VtdDomainId| SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })),
            context_cache: Ghost(Map::empty()),
            structure_caches: Ghost(Map::new(domain_ids, |_did: VtdDomainId| PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() })),
        };
        assert(ret.inv()) by { reveal(IommuTLB::inv); }
        ret
    }

    /// Drops every cached context entry tagged `did`, then empties its IOTLB domain and its paging-structure caches, in the
    /// order VT-d requires: a domain-selective IOTLB invalidation drops the domain's paging-structure-cache entries too
    /// (VT-d 5.20, 6.5.1.2). The root-table lock serializes it with the context-entry update that makes it necessary. The
    /// unit may refill the domain, its paging-structure caches, and the context entries tagged `did` at once with what `k`,
    /// the kernel state whose IOTLB this is, presents.
    #[verifier::external_body]
    pub fn invalidate_domain(&mut self, did: VtdDomainId, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            k.iommu_tlb == *old(self),
            iommu_table_perms_wf(k.it_mp),
            vtd_domain_id_valid(did),
            !lctx.iommu_root_table_lock_map().dom().is_empty(),
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert(did, final(self).spec_index(did)),
            iommu_tlb_within_may_cache(k, did, final(self).spec_index(did)),
            final(self).structure_caches() == old(self).structure_caches().insert(did, final(self).structure_cache(did)),
            iommu_structure_cache_within_may_cache(k, did, final(self).structure_cache(did)),
            Map::new(final(self).context_cache().dom().filter(|bdf: PciBdf| final(self).context_cache()[bdf].1 != did), |bdf: PciBdf| final(self).context_cache()[bdf])
                == Map::new(old(self).context_cache().dom().filter(|bdf: PciBdf| old(self).context_cache()[bdf].1 != did), |bdf: PciBdf| old(self).context_cache()[bdf]),
            forall|bdf: PciBdf| #![trigger final(self).context_cache().dom().contains(bdf)] final(self).context_cache().dom().contains(bdf) && final(self).context_cache()[bdf].1 == did
                ==> iommu_context_cache_entry_present(k, bdf, final(self).context_cache()[bdf]),
    {
        unsafe { veriflat_iommu_invalidate_domain(did); }
        self.domain_tlbs = Ghost(self.domain_tlbs.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
        self.structure_caches = Ghost(self.structure_caches.view().insert(did, PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() }));
        self.context_cache = Ghost(Map::new(self.context_cache.view().dom().filter(|bdf: PciBdf| self.context_cache.view()[bdf].1 != did), |bdf: PciBdf| self.context_cache.view()[bdf]));
    }

    /// Empties only the DID's IOTLB domain and its paging-structure caches (a domain-selective IOTLB invalidation drops both,
    /// VT-d 5.20, 6.5.1.2); the context cache is untouched. The unit may refill the domain and its paging-structure caches
    /// at once with what `k`, the kernel state whose IOTLB this is, presents.
    /// A held IOMMU-table lock serializes it with the leaf update that makes it necessary.
    #[verifier::external_body]
    pub fn invalidate_iotlb_domain(&mut self, did: VtdDomainId, Ghost(k): Ghost<KernelK>, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).inv(),
            k.iommu_tlb == *old(self),
            iommu_table_perms_wf(k.it_mp),
            vtd_domain_id_valid(did),
            !lctx.iommu_table_lock_map().dom().is_empty(),
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().insert(did, final(self).spec_index(did)),
            iommu_tlb_within_may_cache(k, did, final(self).spec_index(did)),
            final(self).structure_caches() == old(self).structure_caches().insert(did, final(self).structure_cache(did)),
            iommu_structure_cache_within_may_cache(k, did, final(self).structure_cache(did)),
            final(self).context_cache() == old(self).context_cache(),
    {
        unsafe { veriflat_iommu_invalidate_iotlb_domain(did); }
        self.domain_tlbs = Ghost(self.domain_tlbs.view().insert(did, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }));
        self.structure_caches = Ghost(self.structure_caches.view().insert(did, PagingStructureCache { pml4e: Map::empty(), pdpte: Map::empty(), pde: Map::empty() }));
    }

    pub closed spec fn view(&self) -> Map<VtdDomainId, SingleTLB> { self.domain_tlbs.view() }

    pub closed spec fn context_cache(&self) -> Map<PciBdf, (PageTableRoot, VtdDomainId)> { self.context_cache.view() }

    /// The paging-structure caches of every domain; K only.
    pub closed spec fn structure_caches(&self) -> Map<VtdDomainId, PagingStructureCache> { self.structure_caches.view() }

    /// The paging-structure caches of domain `did`; K only.
    #[verifier::inline]
    pub open spec fn structure_cache(&self, did: VtdDomainId) -> PagingStructureCache { self.structure_caches().spec_index(did) }

    pub open spec fn spec_index(&self, did: VtdDomainId) -> SingleTLB
        recommends
            self.inv(),
            vtd_domain_id_valid(did),
    {
        self.view().spec_index(did)
    }

    /// One TLB and one paging-structure cache per valid domain ID, and the context cache holds only valid B/D/Fs tagged with
    /// valid domain IDs.
    #[verifier::opaque]
    pub open spec fn inv(&self) -> bool {
        &&& forall|did: VtdDomainId|
            #![trigger self.view().dom().contains(did)]
            self.view().dom().contains(did) <==> vtd_domain_id_valid(did)
        &&& forall|bdf: PciBdf|
            #![trigger self.context_cache().dom().contains(bdf)]
            self.context_cache().dom().contains(bdf)
                ==>
                pci_bdf_valid(bdf.0, bdf.1, bdf.2)
                && vtd_domain_id_valid(self.context_cache()[bdf].1)
        &&& self.structure_caches().dom() == self.view().dom()
    }
}
}
