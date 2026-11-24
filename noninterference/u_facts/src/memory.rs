use vstd::prelude::*;
use veriflat_kernel_core::*;
use crate::*;

verus! {
/// Every 4K, 2M, and 1G page-table leaf and every 4K IOMMU-table leaf of a live process has an address aligned to its size.
#[verifier::opaque]
pub open spec fn kernel_u_leaf_addr_aligned_wf(u: KernelU) -> bool {
    &&& forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_4k[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(va)
            ==> u.process_map[p].pagetable->Some_0.mapping_4k[va].addr % 0x1000 == 0
    &&& forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_2m[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_2m.dom().contains(va)
            ==> u.process_map[p].pagetable->Some_0.mapping_2m[va].addr % 0x200000 == 0
    &&& forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_1g[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_1g.dom().contains(va)
            ==> u.process_map[p].pagetable->Some_0.mapping_1g[va].addr % 0x40000000 == 0
    &&& forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].iommu_table->Some_0.mapping_4k[va]]
        u.process_map.dom().contains(p) && u.process_map[p].iommu_table is Some && u.process_map[p].iommu_table->Some_0.mapping_4k.dom().contains(va)
            ==> u.process_map[p].iommu_table->Some_0.mapping_4k[va].addr % 0x1000 == 0
}

/// The IO-leaf facts give every leaf an address aligned to its size: a RAM leaf names a valid page of its size, a 4K IO leaf
/// a BAR page, and a 2M IO leaf a 2M BAR chunk.
pub proof fn kernel_u_io_leaf_wf_implies_leaf_addr_aligned_wf(u: KernelU)
    requires kernel_u_io_leaf_wf(u),
    ensures kernel_u_leaf_addr_aligned_wf(u),
{
    reveal(kernel_u_io_leaf_wf);
    reveal(kernel_u_leaf_addr_aligned_wf);
    assert(PAGE_SZ_2M == 0x200000) by (compute);
    assert forall|p: RwLockProcessPtr, va: VAddr| #![trigger u.process_map[p].pagetable->Some_0.mapping_4k[va]]
        u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some && u.process_map[p].pagetable->Some_0.mapping_4k.dom().contains(va)
        implies u.process_map[p].pagetable->Some_0.mapping_4k[va].addr % 0x1000 == 0 by {
        let e = u.process_map[p].pagetable->Some_0.mapping_4k[va];
        if e.is_io { bar_page_implies_aligned(u.pci_bars, e.addr); }
    };
}

/// The user projection of a well-formed kernel satisfies `kernel_u_leaf_addr_aligned_wf`.
pub proof fn kernel_inv_implies_u_leaf_addr_aligned_wf(krnl: &KernelK)
    requires krnl.inv(),
    ensures kernel_u_leaf_addr_aligned_wf(kernel_k_to_kernel_u(*krnl)),
{
    kernel_wf_implies_u_ownership_wf(krnl);
    kernel_u_io_leaf_wf_implies_leaf_addr_aligned_wf(kernel_k_to_kernel_u(*krnl));
}

/// The IOTLB caches no 2M or 1G translation, and every domain `did` it caches a 4K translation for has its anchor B/D/F owned
/// by a live process whose IOMMU table, when it has one, carries `did`, and every 4K translation it caches at an IOVA where
/// that table has a present leaf names that leaf's frame, write and execute-disable bits.
#[verifier::opaque]
pub open spec fn kernel_u_iotlb_matches_present_wf(u: KernelU) -> bool {
    &&& forall|did: VtdDomainId| #![trigger u.iommu_tlb[did]] u.iommu_tlb.dom().contains(did) ==> u.iommu_tlb[did].tlb_2m.dom().is_empty() && u.iommu_tlb[did].tlb_1g.dom().is_empty()
    &&& forall|did: VtdDomainId, iova: VAddr| #![trigger u.iommu_tlb[did].tlb_4k.dom().contains(iova)] u.iommu_tlb.dom().contains(did) && u.iommu_tlb[did].tlb_4k.dom().contains(iova) ==> {
        let anchor = pci_bdf_of_did(did);
        let q = u.iommu_root_table.owners[anchor.0 as int][anchor.1 as int][anchor.2 as int];
        let t = u.process_map[q->Some_0].iommu_table;
        &&& q is Some && u.process_map.dom().contains(q->Some_0)
        &&& t is Some ==> t->Some_0.did == Some(did)
        &&& t is Some && t->Some_0.mapping_4k.dom().contains(iova) ==> spec_tlb_entry_equal_to_map_entry(u.iommu_tlb[did].tlb_4k[iova], t->Some_0.mapping_4k[iova])
    }
}

/// For a domain `did` the IOTLB holds in a well-formed kernel: its 2M and 1G maps are empty, and, when it caches a 4K
/// translation, the facts of `kernel_u_iotlb_matches_present_wf` at `did` hold.
pub proof fn kernel_inv_implies_u_iotlb_matches_present_at(krnl: &KernelK, did: VtdDomainId)
    requires krnl.inv(), kernel_k_to_kernel_u(*krnl).iommu_tlb.dom().contains(did),
    ensures
        ({
            let u = kernel_k_to_kernel_u(*krnl);
            let anchor = pci_bdf_of_did(did);
            let q = u.iommu_root_table.owners[anchor.0 as int][anchor.1 as int][anchor.2 as int];
            let t = u.process_map[q->Some_0].iommu_table;
            &&& u.iommu_tlb[did].tlb_2m.dom().is_empty() && u.iommu_tlb[did].tlb_1g.dom().is_empty()
            &&& forall|iova: VAddr| #![trigger u.iommu_tlb[did].tlb_4k.dom().contains(iova)] u.iommu_tlb[did].tlb_4k.dom().contains(iova) ==> {
                &&& q is Some && u.process_map.dom().contains(q->Some_0)
                &&& t is Some ==> t->Some_0.did == Some(did)
                &&& t is Some && t->Some_0.mapping_4k.dom().contains(iova) ==> spec_tlb_entry_equal_to_map_entry(u.iommu_tlb[did].tlb_4k[iova], t->Some_0.mapping_4k[iova])
            }
        }),
{
    reveal(kernel_k_to_kernel_u);
    reveal(iommu_tlb_wf);
    reveal(iommu_root_table_process_wf);
    reveal(page_iommu_table_wf);
    reveal(IommuTLB::inv);
    krnl.irt.view().user_view_eq_owners_and_attached();
    let u = kernel_k_to_kernel_u(*krnl);
    let irt = krnl.irt.view();
    let anchor = pci_bdf_of_did(did);
    assert(vtd_domain_id_valid(did));
    assert(pci_bdf_valid(anchor.0, anchor.1, anchor.2)) by (nonlinear_arith) requires vtd_domain_id_valid(did), anchor == pci_bdf_of_did(did);
    irt.wf_context_entry_at(anchor.0, anchor.1, anchor.2);
    let dtlb = krnl.iommu_tlb.spec_index(did);
    if irt.spec_index_iommu_did(anchor.0, anchor.1, anchor.2) != Some(did) {
        assert(dtlb.is_empty());
        assert forall|iova: VAddr| #![trigger u.iommu_tlb[did].tlb_4k.dom().contains(iova)] !u.iommu_tlb[did].tlb_4k.dom().contains(iova) by { assert(!dtlb.tlb_4k().dom().contains(iova)); };
    } else {
        let owner = irt.spec_index_owner(anchor.0, anchor.1, anchor.2)->Some_0;
        let it = krnl.prc_mp.spec_index(owner).view().iommu_table->Some_0;
        assert(krnl.it_mp.spec_index(it).view().did == Some(did));
        assert(single_tlb_subset_of_pagetable(dtlb, krnl.it_mp.spec_index(it).view()));
        assert forall|iova: VAddr| #![trigger u.iommu_tlb[did].tlb_4k.dom().contains(iova)] u.iommu_tlb[did].tlb_4k.dom().contains(iova) implies {
            let q = u.iommu_root_table.owners[anchor.0 as int][anchor.1 as int][anchor.2 as int];
            let t = u.process_map[q->Some_0].iommu_table;
            &&& q is Some && u.process_map.dom().contains(q->Some_0)
            &&& t is Some ==> t->Some_0.did == Some(did)
            &&& t is Some && t->Some_0.mapping_4k.dom().contains(iova) ==> spec_tlb_entry_equal_to_map_entry(u.iommu_tlb[did].tlb_4k[iova], t->Some_0.mapping_4k[iova])
        } by {
            assert(dtlb.tlb_4k().dom().contains(iova));
            assert(krnl.it_mp.spec_index(it).view().mapping_4k().contains_key(iova));
        };
    }
}

/// The user projection of a well-formed kernel satisfies `kernel_u_iotlb_matches_present_wf`.
pub proof fn kernel_inv_implies_u_iotlb_matches_present_wf(krnl: &KernelK)
    requires krnl.inv(),
    ensures kernel_u_iotlb_matches_present_wf(kernel_k_to_kernel_u(*krnl)),
{
    let u = kernel_k_to_kernel_u(*krnl);
    reveal(kernel_u_iotlb_matches_present_wf);
    assert forall|did: VtdDomainId| #![trigger u.iommu_tlb[did]] u.iommu_tlb.dom().contains(did) implies u.iommu_tlb[did].tlb_2m.dom().is_empty() && u.iommu_tlb[did].tlb_1g.dom().is_empty() by {
        kernel_inv_implies_u_iotlb_matches_present_at(krnl, did);
    };
    assert forall|did: VtdDomainId, iova: VAddr| #![trigger u.iommu_tlb[did].tlb_4k.dom().contains(iova)] u.iommu_tlb.dom().contains(did) && u.iommu_tlb[did].tlb_4k.dom().contains(iova) implies {
        let anchor = pci_bdf_of_did(did);
        let q = u.iommu_root_table.owners[anchor.0 as int][anchor.1 as int][anchor.2 as int];
        let t = u.process_map[q->Some_0].iommu_table;
        &&& q is Some && u.process_map.dom().contains(q->Some_0)
        &&& t is Some ==> t->Some_0.did == Some(did)
        &&& t is Some && t->Some_0.mapping_4k.dom().contains(iova) ==> spec_tlb_entry_equal_to_map_entry(u.iommu_tlb[did].tlb_4k[iova], t->Some_0.mapping_4k[iova])
    } by { kernel_inv_implies_u_iotlb_matches_present_at(krnl, did); assert(u.iommu_tlb[did].tlb_4k[iova] == u.iommu_tlb[did].tlb_4k[iova]); };
}
}
