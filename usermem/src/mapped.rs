//! The safety link to the kernel's page state: in the user projection of a well-formed kernel, every pending store and every
//! device write targets a frame that the writer's own table maps at the address it writes through.
use vstd::prelude::*;
use crate::*;
use crate::invariant::*;

verus! {
/// In the user projection of a well-formed kernel, a pending store of cpu `c` targets a frame that a leaf of its cpu's current
/// process's page table maps at the store's VA, present or hidden: a BAR page or chunk, or a page in the mapped state of the
/// store's page size whose mappings list (that table, the store's VA).
pub proof fn kernel_inv_implies_pending_store_frame_mapped(krnl: KernelK, st: MemState, c: CpuId, j: int)
    requires krnl.inv(), st.u == kernel_k_to_kernel_u(krnl), store_buffers_covered(st), index_valid(NUM_CPUS, c), 0 <= j < st.bufs[c as int].len(),
    ensures
        ({
            let s = st.bufs[c as int][j];
            let p = st.u.cpu_array[c as int].current_process->Some_0;
            &&& st.u.cpu_array[c as int].current_process is Some && st.u.process_map[p].pcid == s.pcid
            &&& kernel_frame_mapped_by_pagetable_at(krnl, krnl.prc_mp.spec_index(p).view().pagetable, s.size, s.base_va, s.frame)
        }),
{
    let s = st.bufs[c as int][j];
    assert(store_covered(st.u, c, s));
    assert(tlb_of_size(st.u.cpu_tlb[(c, s.pcid)], s.size) == single_tlb_entries_of_size(st.u.cpu_tlb[(c, s.pcid)], s.size));
    kernel_inv_implies_usable_tlb_entry_names_mapped_page(&krnl, c, s.size, s.base_va);
}

/// In the user projection of a well-formed kernel, a device write of a domain `did` that the IOTLB holds targets a page in the
/// Mapped4k state whose IOMMU mappings list (`it`, `iova`), where `it` is the IOMMU table carrying `did`, owned by the process
/// owning the B/D/F that anchors `did`.
pub proof fn kernel_inv_implies_dma_write_frame_iommu_mapped(krnl: KernelK, old: MemState, new: MemState, did: VtdDomainId, iova: VAddr, frame: PAddr,
    offset: nat, bytes: Seq<u8>, c: CpuId)
    requires krnl.inv(), old.u == kernel_k_to_kernel_u(krnl), old.u.iommu_tlb.dom().contains(did), mem_step(old, new, MemLabel::DmaWritten { did, iova, frame, offset, bytes }, c),
    ensures
        ({
            let anchor = pci_bdf_of_did(did);
            let owner = krnl.irt.view().spec_index_owner(anchor.0, anchor.1, anchor.2)->Some_0;
            let it = krnl.prc_mp.spec_index(owner).view().iommu_table->Some_0;
            let pg = page_ptr2page_index(frame);
            &&& krnl.irt.view().spec_index_owner(anchor.0, anchor.1, anchor.2) is Some && krnl.prc_mp.spec_index(owner).view().iommu_table is Some
            &&& krnl.it_mp.dom().contains(it) && krnl.it_mp.spec_index(it).view().did == Some(did)
            &&& index_valid(NUM_PAGES, pg) && page_index2page_ptr(pg) == frame
            &&& krnl.pg_arr.spec_index(pg).view().view().state == PageState::Mapped4k
            &&& krnl.pg_arr.spec_index(pg).view().view().iommu_mappings().contains((it, iova))
        }),
{ kernel_inv_implies_iotlb_entry_names_iommu_mapped_page(&krnl, did, iova); }
} // verus!
