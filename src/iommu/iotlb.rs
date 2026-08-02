use vstd::prelude::*;

verus! {

use crate::*;

pub type Iova = usize;
pub type VtdDomainId = usize;

/// The current kernel model has one VT-d remapping unit and therefore one
/// global IOTLB.  Generalizing this becomes an array indexed by unit id.
pub const VTD_DOMAIN_COUNT: usize = 65_536;

pub open spec fn vtd_domain_id_valid(did: VtdDomainId) -> bool {
    did < VTD_DOMAIN_COUNT
}

/// VT-d second-level addresses use the physical-address-width and alignment
/// constraints of the selected page size.  They are not CPU kernel virtual
/// addresses and therefore must not use the kernel-L4-range VA predicates.
pub open spec fn iova_4k_valid(iova: Iova) -> bool {
    iova & (!MEM_4K_MASK) as usize == 0
}

pub open spec fn iova_2m_valid(iova: Iova) -> bool {
    iova & (!MEM_2M_MASK) as usize == 0
}

pub open spec fn iova_1g_valid(iova: Iova) -> bool {
    iova & (!MEM_1G_MASK) as usize == 0
}

/// Cached translations for one VT-d domain.  As with the CPU TLB model, the
/// three maps retain the page size of the translation from which an entry was
/// filled.
pub ghost struct SingleIotlb {
    pub entries_4k: Map<Iova, TLBEntry>,
    pub entries_2m: Map<Iova, TLBEntry>,
    pub entries_1g: Map<Iova, TLBEntry>,
}

impl SingleIotlb {
    pub open spec fn entries_4k(&self) -> Map<Iova, TLBEntry> {
        self.entries_4k
    }

    pub open spec fn entries_2m(&self) -> Map<Iova, TLBEntry> {
        self.entries_2m
    }

    pub open spec fn entries_1g(&self) -> Map<Iova, TLBEntry> {
        self.entries_1g
    }

    pub open spec fn is_empty(&self) -> bool {
        &&& self.entries_4k().dom() == Set::<Iova>::empty()
        &&& self.entries_2m().dom() == Set::<Iova>::empty()
        &&& self.entries_1g().dom() == Set::<Iova>::empty()
    }

    /// Invalidation may be performed at a coarser granularity than requested,
    /// so its abstract effect is monotonic removal, not exact map equality.
    pub open spec fn submap_of(&self, old: &Self) -> bool {
        &&& self.entries_4k().submap_of(old.entries_4k())
        &&& self.entries_2m().submap_of(old.entries_2m())
        &&& self.entries_1g().submap_of(old.entries_1g())
    }
}

/// One logical IOTLB for the single VT-d remapping unit currently modeled by
/// VeriFlat.  Entries are tagged by DID, not by CPU.  The VT-d context cache
/// and endpoint ATS/device-TLB caches are intentionally separate future state.
pub struct IommuTLB {
    pub domain_tlbs: Ghost<Map<VtdDomainId, SingleIotlb>>,
}

impl IommuTLB {
    pub open spec fn view(&self) -> Map<VtdDomainId, SingleIotlb> {
        self.domain_tlbs@
    }

    pub open spec fn spec_index(&self, did: VtdDomainId) -> SingleIotlb
        recommends
            self.inv(),
            vtd_domain_id_valid(did),
    {
        self.view()[did]
    }

    pub open spec fn inv(&self) -> bool {
        forall|did: VtdDomainId|
            #![trigger self.view().dom().contains(did)]
            self.view().dom().contains(did) <==> vtd_domain_id_valid(did)
    }

    pub open spec fn invalidation_only_removes(&self, old: &Self) -> bool {
        &&& self.inv()
        &&& old.inv()
        &&& forall|did: VtdDomainId|
            #![trigger self.spec_index(did)]
            vtd_domain_id_valid(did)
            ==> self.spec_index(did).submap_of(&old.spec_index(did))
    }

    pub open spec fn invalidate_global_ensures(&self, old: &Self) -> bool {
        &&& self.invalidation_only_removes(old)
        &&& forall|did: VtdDomainId|
            #![trigger self.spec_index(did)]
            vtd_domain_id_valid(did)
            ==> self.spec_index(did).is_empty()
    }

    pub open spec fn invalidate_domain_ensures(
        &self,
        old: &Self,
        did: VtdDomainId,
    ) -> bool {
        &&& vtd_domain_id_valid(did)
        &&& self.invalidation_only_removes(old)
        &&& self.spec_index(did).is_empty()
    }

    pub open spec fn page_invalidation_target_absent(
        &self,
        did: VtdDomainId,
        iova: Iova,
        page_size: PageSize,
    ) -> bool
        recommends
            self.inv(),
            vtd_domain_id_valid(did),
    {
        match page_size {
            PageSize::SZ4k => {
                &&& iova_4k_valid(iova)
                &&& !self.spec_index(did).entries_4k().dom().contains(iova)
            },
            PageSize::SZ2m => {
                &&& iova_2m_valid(iova)
                &&& !self.spec_index(did).entries_2m().dom().contains(iova)
            },
            PageSize::SZ1g => {
                &&& iova_1g_valid(iova)
                &&& !self.spec_index(did).entries_1g().dom().contains(iova)
            },
        }
    }

    pub open spec fn invalidate_page_ensures(
        &self,
        old: &Self,
        did: VtdDomainId,
        iova: Iova,
        page_size: PageSize,
    ) -> bool {
        &&& vtd_domain_id_valid(did)
        &&& self.invalidation_only_removes(old)
        &&& self.page_invalidation_target_absent(did, iova, page_size)
    }
}

}
