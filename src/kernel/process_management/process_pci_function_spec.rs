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
}
