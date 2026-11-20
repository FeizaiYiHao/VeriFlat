use vstd::prelude::*;
use crate::*;

verus! {
/// The root table's owners and the page tables' PCI function arrays agree: an owned function sits in the array of its
/// owner's page table, and a function in a page table's array is owned by that table's process. Both sides change only
/// under the page-table lock and the root-table lock together.
#[verifier::opaque]
pub open spec fn pci_function_ownership_wf(irt: IommuRootTable, prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap) -> bool {
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger irt.spec_index_owner(bus, device, function)]
        pci_bdf_valid(bus, device, function) && irt.spec_index_owner(bus, device, function) is Some ==> {
            let p = irt.spec_index_owner(bus, device, function)->Some_0;
            &&& prc_mp.dom().contains(p)
            &&& pt_mp.dom().contains(prc_mp.spec_index(p).view().pagetable)
            &&& pt_mp.spec_index(prc_mp.spec_index(p).view().pagetable).view().higher.pci.view().dom().contains((bus, device, function))
        }
    &&& forall|pt: RwLockPageTableRoot, f: PciBdf|
        #![trigger pt_mp.spec_index(pt).view().higher.pci.view().dom().contains(f)]
        pt_mp.dom().contains(pt) && pt_mp.spec_index(pt).view().higher.pci.view().dom().contains(f)
            ==> pci_bdf_valid(f.0, f.1, f.2) && irt.spec_index_owner(f.0, f.1, f.2) == Some(pt_mp.spec_index(pt).view().higher.proc_ptr)
}

/// `pci_function_ownership_wf` at the owned function `(bus, device, function)`.
pub proof fn pci_function_ownership_wf_function_at(irt: IommuRootTable, prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, bus: usize, device: usize, function: usize)
    requires
        pci_function_ownership_wf(irt, prc_mp, pt_mp),
        pci_bdf_valid(bus, device, function),
        irt.spec_index_owner(bus, device, function) is Some,
    ensures
        ({
            let p = irt.spec_index_owner(bus, device, function)->Some_0;
            &&& prc_mp.dom().contains(p)
            &&& pt_mp.dom().contains(prc_mp.spec_index(p).view().pagetable)
            &&& pt_mp.spec_index(prc_mp.spec_index(p).view().pagetable).view().higher.pci.view().dom().contains((bus, device, function))
        }),
{ reveal(pci_function_ownership_wf); }

/// `pci_function_ownership_wf` at the function `f` in the array of page table `pt`.
pub proof fn pci_function_ownership_wf_pagetable_at(irt: IommuRootTable, prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, pt: RwLockPageTableRoot, f: PciBdf)
    requires
        pci_function_ownership_wf(irt, prc_mp, pt_mp),
        pt_mp.dom().contains(pt),
        pt_mp.spec_index(pt).view().higher.pci.view().dom().contains(f),
    ensures
        pci_bdf_valid(f.0, f.1, f.2),
        irt.spec_index_owner(f.0, f.1, f.2) == Some(pt_mp.spec_index(pt).view().higher.proc_ptr),
{ reveal(pci_function_ownership_wf); }

/// `iommu_root_table_process_wf` and `pci_function_ownership_wf` at the IOMMU table `it_ptr`: the anchor of its DID, if any, is
/// a valid function owned by the table's process and held in the PCI function array of that process's page table.
pub proof fn iommu_root_table_process_and_pci_function_ownership_wf_table_at(
    irt: IommuRootTable, prc_mp: ProcessLockedMap, it_mp: IommuTableLockedMap, pt_mp: PageTableLockedMap, it_ptr: RwLockPageTableRoot,
)
    requires
        iommu_root_table_process_wf(irt, prc_mp, it_mp),
        pci_function_ownership_wf(irt, prc_mp, pt_mp),
        it_mp.dom().contains(it_ptr),
    ensures
        it_mp.spec_index(it_ptr).view().did is Some ==> {
            let table = it_mp.spec_index(it_ptr).view();
            let anchor = pci_bdf_of_did(table.did->Some_0);
            &&& pci_bdf_valid(anchor.0, anchor.1, anchor.2)
            &&& irt.spec_index_owner(anchor.0, anchor.1, anchor.2) == Some(table.proc_ptr)
            &&& prc_mp.dom().contains(table.proc_ptr)
            &&& pt_mp.spec_index(prc_mp.spec_index(table.proc_ptr).view().pagetable).view().higher.pci.view().dom().contains(anchor)
        },
{
    reveal(iommu_root_table_process_wf);
    reveal(pci_function_ownership_wf);
    if let Some(did) = it_mp.spec_index(it_ptr).view().did {
        assert(pci_bdf_valid(pci_bdf_of_did(did).0, pci_bdf_of_did(did).1, pci_bdf_of_did(did).2)) by (nonlinear_arith) requires vtd_domain_id_valid(did);
    }
}
}
