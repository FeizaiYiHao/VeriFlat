use vstd::prelude::*;
use crate::*;

verus! {
/// Attaching a function owned by a live process with an IOMMU table keeps the root-table, ownership,
/// and IOTLB invariants: its translation is that table's root, and its IOTLB domain was empty while detached.
pub(super) proof fn pci_attach_dma_eof(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, bus: usize, device: usize, function: usize, root: PageTableRoot)
    requires
        pre.inv(),
        post == (KernelK { irt: post.irt, ..pre }),
        post.irt.inv(),
        pci_bdf_valid(bus, device, function),
        post.irt.view().owners() == pre.irt.view().owners(),
        forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f) ==> {
            &&& post.irt.view().spec_index_owner(b, d, f) == pre.irt.view().spec_index_owner(b, d, f)
            &&& post.irt.view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { Some(root) } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
        },
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().iommu_cr3 == Some(root),
        pre.irt.view().spec_index_owner(bus, device, function) == process_ptr,
        pre.prc_mp.spec_index(process_ptr).view().iommu_table is Some ==> !(pre.it_mp.spec_index(pre.prc_mp.spec_index(process_ptr).view().iommu_table->Some_0).locking_thread() is Write),
    ensures
        post.inv(),
{
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); reveal(process_iommu_table_match); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); reveal(process_iommu_table_match); };
    assert(post.inv()) by { reveal(KernelK::default_pagetable_wf); };
}
} // verus!
