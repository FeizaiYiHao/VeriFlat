use vstd::prelude::*;

verus! {
use crate::*;

/// The global IOTLB is indexed by DID and the context cache by B/D/F.  Ownership,
/// root/table/DID agreement, and DID anchoring live in `iommu_root_table_process_wf`;
/// this predicate only constrains cached state.  A cached context entry equals the
/// current present entry's root and DID (`CAP.CM = 0`).  A present entry's DID
/// domain is its owner table's DID domain.  A candidate DID whose anchor
/// `pci_bdf_of_did(did)` does not carry it is inactive, and its domain is empty.
/// Detach clears the entry and invalidates its DID in the same section under the
/// root-table lock, so the predicate holds again at the section end.  The IOMMU
/// table's write lock is the dirty marker: an attached domain of a table that is
/// not write-locked caches only present leaves.  The write holder may hide leaves
/// while attached and re-establishes this with an IOTLB flush before unlocking.
// Proof dependency (confirmed): iommu_root_table_process_wf.
#[verifier::opaque]
pub open spec fn iommu_tlb_wf(iommu_tlb: IommuTLB, root_table: IommuRootTable, process_map: ProcessLockedMap, iommu_table_map: IommuTableLockedMap) -> bool {
    &&& iommu_tlb.inv()
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        #![trigger root_table.spec_index_iommu_root(bus, device, function)]
        pci_bdf_valid(bus, device, function) && root_table.spec_index_iommu_root(bus, device, function) is Some ==> {
            let proc_ptr = root_table.spec_index_owner(bus, device, function)->Some_0;
            let iommu_table = iommu_table_map.spec_index(process_map.spec_index(proc_ptr).view().iommu_table.unwrap());
            let domain_tlb = iommu_tlb.spec_index(iommu_table.view().did->Some_0);
            &&& single_tlb_subset_of_pagetable(domain_tlb, iommu_table.view())
            &&& !(iommu_table.locking_thread() is Write) ==> single_tlb_subset_of_present_pagetable(domain_tlb, iommu_table.view())
        }
    &&& forall|did: VtdDomainId|
        #![trigger iommu_tlb.spec_index(did)]
        vtd_domain_id_valid(did) ==> {
            let anchor = pci_bdf_of_did(did);
            root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) != Some(did) ==> iommu_tlb.spec_index(did).is_empty()
        }
    &&& forall|bdf: PciBdf|
        #![trigger iommu_tlb.context_cache().dom().contains(bdf)]
        iommu_tlb.context_cache().dom().contains(bdf) ==> {
            &&& root_table.spec_index_iommu_root(bdf.0, bdf.1, bdf.2) == Some(iommu_tlb.context_cache()[bdf].0)
            &&& root_table.spec_index_iommu_did(bdf.0, bdf.1, bdf.2) == Some(iommu_tlb.context_cache()[bdf].1)
        }
}

/// Each domain's paging-structure caches keep only present non-leaf entries of the IOMMU table that carries its DID, and a
/// DID its anchor does not carry caches none. An attached table never clears a present non-leaf entry, so no lock exemption.
// Proof dependency (confirmed): iommu_root_table_process_wf, process_iommu_table_wf.
#[verifier::opaque]
pub open spec fn iommu_structure_cache_wf(iommu_tlb: IommuTLB, root_table: IommuRootTable, iommu_table_map: IommuTableLockedMap) -> bool {
    &&& forall|it: RwLockPageTableRoot| #![trigger iommu_table_map.spec_index(it).view().did]
        iommu_table_map.dom().contains(it) && iommu_table_map.spec_index(it).view().did is Some
            ==> single_structure_cache_subset_of_present_iommu_table(iommu_tlb.structure_cache(iommu_table_map.spec_index(it).view().did->Some_0), iommu_table_map.spec_index(it).view())
    &&& forall|did: VtdDomainId| #![trigger iommu_tlb.structure_cache(did)]
        vtd_domain_id_valid(did) ==> {
            let anchor = pci_bdf_of_did(did);
            root_table.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) != Some(did) ==> iommu_tlb.structure_cache(did).is_empty()
        }
}

/// `iommu_structure_cache_wf` at the IOMMU table `it` and at the DID `did`.
pub proof fn iommu_structure_cache_wf_at(iommu_tlb: IommuTLB, root_table: IommuRootTable, iommu_table_map: IommuTableLockedMap, it: RwLockPageTableRoot, did: VtdDomainId)
    requires iommu_structure_cache_wf(iommu_tlb, root_table, iommu_table_map),
    ensures
        iommu_table_map.dom().contains(it) && iommu_table_map.spec_index(it).view().did is Some
            ==> single_structure_cache_subset_of_present_iommu_table(iommu_tlb.structure_cache(iommu_table_map.spec_index(it).view().did->Some_0), iommu_table_map.spec_index(it).view()),
        vtd_domain_id_valid(did) && root_table.spec_index_iommu_did(pci_bdf_of_did(did).0, pci_bdf_of_did(did).1, pci_bdf_of_did(did).2) != Some(did)
            ==> iommu_tlb.structure_cache(did).is_empty(),
{ reveal(iommu_structure_cache_wf); }

/// No IOMMU cache names table page `page`: no domain's paging-structure caches keep an L4, L3, or L2 entry pointing at it,
/// and no cached context entry has it as its root.
pub open spec fn iommu_page_unreferenced_by_iommu_caches(iommu_tlb: IommuTLB, page: PageMapPtr) -> bool {
    &&& forall|did: VtdDomainId| #![trigger iommu_tlb.structure_cache(did)]
        vtd_domain_id_valid(did) ==> {
            let cache = iommu_tlb.structure_cache(did);
            &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] cache.pml4e.dom().contains(i) ==> cache.pml4e.spec_index(i) != page
            &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] cache.pdpte.dom().contains(key) ==> cache.pdpte.spec_index(key) != page
            &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] cache.pde.dom().contains(key) ==> cache.pde.spec_index(key) != page
        }
    &&& forall|bdf: PciBdf| #![trigger iommu_tlb.context_cache().dom().contains(bdf)]
        iommu_tlb.context_cache().dom().contains(bdf) ==> iommu_tlb.context_cache()[bdf].0 != page
}

/// A page of an IOMMU table without a DID is named by no IOMMU cache: a non-empty paging-structure cache belongs to an
/// active DID, whose table holds the cached entries and is another table with a disjoint page closure, and a cached
/// context entry is a present context entry whose root is the root of a table with a DID.
pub proof fn iommu_table_without_did_implies_page_unreferenced_by_iommu_caches(k: KernelK, it: RwLockPageTableRoot, page: PageMapPtr)
    requires
        k.inv(),
        k.it_mp.dom().contains(it),
        k.it_mp.spec_index(it).view().page_closure().contains(page),
        k.it_mp.spec_index(it).view().did is None,
    ensures iommu_page_unreferenced_by_iommu_caches(k.iommu_tlb, page),
{
    broadcast use iommu_table_without_did_implies_page_unreferenced_by_iommu_caches_at;
    reveal(IommuTLB::inv); reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf);
}

/// The root of an IOMMU table without a DID is named by no present context entry: such an entry names the root of a table
/// with a DID, whose anchor carries it with the same root, and the point form below excludes that root.
pub proof fn iommu_table_without_did_implies_root_named_by_no_context_entry(k: KernelK, it: RwLockPageTableRoot)
    requires
        k.inv(),
        k.it_mp.dom().contains(it),
        k.it_mp.spec_index(it).view().did is None,
    ensures
        forall|b: usize, d: usize, f: usize| #![trigger k.irt.view().spec_index_iommu_root(b, d, f)]
            pci_bdf_valid(b, d, f) ==> k.irt.view().spec_index_iommu_root(b, d, f) != Some(k.it_mp.spec_index(it).view().cr3),
{
    assert(k.it_mp.spec_index(it).view().page_closure().contains(k.it_mp.spec_index(it).view().cr3)) by { iommu_table_perms_wf_at(k.it_mp, it); reveal(IommuTable::wf_l4); };
    broadcast use iommu_table_without_did_implies_page_unreferenced_by_iommu_caches_at;
    reveal(iommu_root_table_process_wf);
}

/// Point form of `iommu_table_without_did_implies_page_unreferenced_by_iommu_caches` at one DID: its paging-structure caches
/// name no page of the table, and when its anchor B/D/F carries it, the anchor's root is no such page. A cached context
/// entry is present with a valid DID whose anchor carries it and has the same root, so both halves trigger on the DID.
pub broadcast proof fn iommu_table_without_did_implies_page_unreferenced_by_iommu_caches_at(k: KernelK, it: RwLockPageTableRoot, page: PageMapPtr, did: VtdDomainId)
    requires
        k.inv(),
        k.it_mp.dom().contains(it),
        k.it_mp.spec_index(it).view().page_closure().contains(page),
        k.it_mp.spec_index(it).view().did is None,
    ensures
        #![trigger vtd_domain_id_valid(did), k.it_mp.spec_index(it).view().page_closure().contains(page)]
        vtd_domain_id_valid(did) ==> {
            let cache = k.iommu_tlb.structure_cache(did);
            let anchor = pci_bdf_of_did(did);
            &&& forall|i: L4Index| #![trigger cache.pml4e.dom().contains(i)] cache.pml4e.dom().contains(i) ==> cache.pml4e.spec_index(i) != page
            &&& forall|key: (L4Index, L3Index)| #![trigger cache.pdpte.dom().contains(key)] cache.pdpte.dom().contains(key) ==> cache.pdpte.spec_index(key) != page
            &&& forall|key: (L4Index, L3Index, L2Index)| #![trigger cache.pde.dom().contains(key)] cache.pde.dom().contains(key) ==> cache.pde.spec_index(key) != page
            &&& k.irt.view().spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did) ==> k.irt.view().spec_index_iommu_root(anchor.0, anchor.1, anchor.2) != Some(page)
        },
{
    let irt = k.irt.view();
    let anchor = pci_bdf_of_did(did);
    iommu_table_pages_wf_closure_page_at(k.it_mp, k.pg_arr, it, page);
    iommu_structure_cache_wf_at(k.iommu_tlb, irt, k.it_mp, it, did);
    if vtd_domain_id_valid(did) && irt.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(did) {
        let other = k.prc_mp.spec_index(irt.spec_index_owner(anchor.0, anchor.1, anchor.2)->Some_0).view().iommu_table->Some_0;
        let table = k.it_mp.spec_index(other).view();
        irt.wf_context_entry_at(anchor.0, anchor.1, anchor.2); iommu_root_table_process_wf_function_at(irt, k.prc_mp, k.it_mp, anchor.0, anchor.1, anchor.2);
        iommu_structure_cache_wf_at(k.iommu_tlb, irt, k.it_mp, other, did);
        iommu_table_perms_wf_at(k.it_mp, other);
        reveal(IommuTable::wf_l4); reveal(IommuTable::wf_l3); reveal(IommuTable::wf_l2);
        if table.page_closure().contains(page) { iommu_table_pages_wf_closure_page_at(k.it_mp, k.pg_arr, other, page); }
    }
}

/// The DID domain of IOMMU table `it` caches only present leaves of `it`: the write holder's flush establishes it and the
/// step boundary keeps it.  A table without a DID constrains nothing; its domain-emptiness lives in `iommu_tlb_wf`.
/// Opaque: callers forward it unchanged; only the flush producer and the EOF closures that relate it to `iommu_tlb_wf` reveal it.
#[verifier::opaque]
pub open spec fn iommu_table_tlb_entries_present(iommu_tlb: IommuTLB, root_table: IommuRootTable, iommu_table_map: IommuTableLockedMap, it: RwLockPageTableRoot) -> bool {
    iommu_table_map.spec_index(it).view().did matches Some(did) ==> single_tlb_subset_of_present_pagetable(iommu_tlb.spec_index(did), iommu_table_map.spec_index(it).view())
}

/// Every pending DMA request names a valid domain and is still translated by the 4K IOTLB entry of that domain at its IOVA,
/// with its frame, and a write request by a writable one.
#[verifier::opaque]
pub open spec fn pending_dma_covered_by_iotlb(iommu_tlb: IommuTLB) -> bool {
    forall|r: PendingDma| #![trigger iommu_tlb.pending_dma().contains(r)]
        iommu_tlb.pending_dma().contains(r) ==> {
            let tlb = iommu_tlb.spec_index(r.did).tlb_4k();
            &&& vtd_domain_id_valid(r.did)
            &&& tlb.dom().contains(r.iova)
            &&& tlb[r.iova].addr == r.frame
            &&& r.write ==> tlb[r.iova].write
        }
}

/// The pending DMA request `r` is covered by the IOTLB entry of its domain.
pub proof fn pending_dma_covered_by_iotlb_at(iommu_tlb: IommuTLB, r: PendingDma)
    requires
        pending_dma_covered_by_iotlb(iommu_tlb),
        iommu_tlb.pending_dma().contains(r),
    ensures
        ({
            let tlb = iommu_tlb.spec_index(r.did).tlb_4k();
            &&& vtd_domain_id_valid(r.did)
            &&& tlb.dom().contains(r.iova)
            &&& tlb[r.iova].addr == r.frame
            &&& r.write ==> tlb[r.iova].write
        }),
{ reveal(pending_dma_covered_by_iotlb); }
}
