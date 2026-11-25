use vstd::prelude::*;
use crate::*;

verus! {
/// The pending user store `s` of cpu `c` writes the page that its cpu's dirty table maps at the store's size, or a page of a
/// PCI BAR (a store through an IO leaf): a cpu with a pending store is outside a kernel step, so it runs its recorded PCID,
/// whose TLB keeps only non-empty leaves of that table.
pub broadcast proof fn kernel_inv_implies_pending_store_target_mapped_or_bar_page_at(k: KernelK, c: CpuId, s: PendingStore)
    requires
        k.inv(),
        index_valid(NUM_CPUS, c),
        #[trigger] k.cpu_op.view().store_buffer(c).contains(s),
    ensures
        ({
            let pg_idx = page_ptr2page_index(s.frame);
            ||| index_valid(NUM_PAGES, pg_idx) && k.pg_arr.spec_index(pg_idx).view().view().state
                == match s.size { PageSize::SZ4k => PageState::Mapped4k, PageSize::SZ2m => PageState::Mapped2m, PageSize::SZ1g => PageState::Mapped1g }
            ||| pci_bar_page(k.pci_bars.view(), s.frame)
        }),
{
    let pt = k.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(s.pcid).unwrap().pagetable_ptr;
    let va = s.base_va;
    store_buffers_empty_in_step_or_off_at(k.cpu_op.view(), c);
    pending_stores_covered_by_tlb_at(k.cpu_op.view(), k.cpu_hw_cr3_pcid, k.cpu_tlb, c, s);
    cpu_hw_cr3_pcid_wf_at(k.cpu_hw_cr3_pcid, k.cpu_arr, k.pcid_needflush, k.cpu_op.view().view(), c);
    assert(k.pt_mp.dom().contains(pt) && single_tlb_subset_of_whole_pagetable(k.cpu_tlb.spec_index((c, s.pcid)), whole_pagetable(k.pt_mp, k.pt_lower.view(), pt))) by {
        reveal(cpu_tlb_wf);
    };
    broadcast use spec_va_4k_valid_index_roundtrip, spec_va_2m_valid_index_roundtrip, spec_va_1g_valid_index_roundtrip;
    match s.size {
        PageSize::SZ4k => {
            mapped_4k_page_pagetable_wf_nonempty_leaf_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, pt, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
            pagetable_pci_mappings_wf_nonempty_4k_at(k.pci_bars.view(), k.pt_mp, k.pt_lower.view(), pt, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
        },
        PageSize::SZ2m => {
            mapped_2m_page_pagetable_wf_nonempty_leaf_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, pt, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
            pagetable_pci_mappings_wf_nonempty_2m_at(k.pci_bars.view(), k.pt_mp, k.pt_lower.view(), pt, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va));
        },
        PageSize::SZ1g => { mapped_1g_page_pagetable_wf_nonempty_leaf_at(k.pt_mp, k.pt_lower.view(), k.pg_arr, pt, spec_v2l4index(va), spec_v2l3index(va)); },
    }
}

/// The pending DMA request `r` reaches a Mapped4k page: its valid domain caches a translation, so the domain's anchor B/D/F
/// carries it and the domain's IOTLB keeps only 4K leaves of the IOMMU table of the anchor's owner.
pub broadcast proof fn kernel_inv_implies_pending_dma_target_mapped_4k_page_at(k: KernelK, r: PendingDma)
    requires
        k.inv(),
        #[trigger] k.iommu_tlb.pending_dma().contains(r),
    ensures index_valid(NUM_PAGES, page_ptr2page_index(r.frame)) && k.pg_arr.spec_index(page_ptr2page_index(r.frame)).view().view().state == PageState::Mapped4k,
{
    let anchor = pci_bdf_of_did(r.did);
    let owner = k.irt.view().spec_index_owner(anchor.0, anchor.1, anchor.2)->Some_0;
    let it = k.prc_mp.spec_index(owner).view().iommu_table->Some_0;
    pending_dma_covered_by_iotlb_at(k.iommu_tlb, r);
    assert(pci_bdf_valid(anchor.0, anchor.1, anchor.2)) by (nonlinear_arith) requires vtd_domain_id_valid(r.did), anchor == pci_bdf_of_did(r.did);
    assert(k.irt.view().spec_index_iommu_did(anchor.0, anchor.1, anchor.2) == Some(r.did)) by { reveal(iommu_tlb_wf); };
    assert(k.it_mp.dom().contains(it) && k.it_mp.spec_index(it).view().mapping_4k().contains_key(r.iova) && k.it_mp.spec_index(it).view().mapping_4k().spec_index(r.iova).addr == r.frame) by {
        reveal(iommu_root_table_process_wf); k.irt.view().wf_context_entry_at(anchor.0, anchor.1, anchor.2); reveal(iommu_tlb_wf);
    };
    page_iommu_table_wf_table_at(k.ctn_mp, k.prc_mp, k.it_mp, k.pg_arr, it, r.iova);
    iommu_table_perms_wf_at(k.it_mp, it);
    page_ptr_valid_imply_page_index_valid();
}

/// Under the kernel invariant every pending write reaches a page the kernel hands to user space: (a) each pending user store
/// of a cpu writes a page in state Mapped of the store's size or a page of a PCI BAR, and (b) each pending DMA request reaches
/// a Mapped4k page. No caller by nature.
pub proof fn kernel_inv_implies_pending_writes_target_mapped_or_bar_pages(k: KernelK)
    requires k.inv(),
    ensures
        forall|c: CpuId, s: PendingStore| #![trigger k.cpu_op.view().store_buffer(c).contains(s)]
            index_valid(NUM_CPUS, c) && k.cpu_op.view().store_buffer(c).contains(s) ==> {
                let pg_idx = page_ptr2page_index(s.frame);
                ||| index_valid(NUM_PAGES, pg_idx) && k.pg_arr.spec_index(pg_idx).view().view().state
                    == match s.size { PageSize::SZ4k => PageState::Mapped4k, PageSize::SZ2m => PageState::Mapped2m, PageSize::SZ1g => PageState::Mapped1g }
                ||| pci_bar_page(k.pci_bars.view(), s.frame)
            },
        forall|r: PendingDma| #![trigger k.iommu_tlb.pending_dma().contains(r)]
            k.iommu_tlb.pending_dma().contains(r) ==> index_valid(NUM_PAGES, page_ptr2page_index(r.frame)) && k.pg_arr.spec_index(page_ptr2page_index(r.frame)).view().view().state == PageState::Mapped4k,
{ broadcast use kernel_inv_implies_pending_store_target_mapped_or_bar_page_at, kernel_inv_implies_pending_dma_target_mapped_4k_page_at; }
}
