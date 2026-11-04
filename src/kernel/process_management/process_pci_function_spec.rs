use vstd::prelude::*;
use crate::*;

verus! {
/// Bidirectional ownership index between the static BDF metadata table and
/// each process's lock-free ghost reverse set.  Both directions change only
/// under the root-table lock.
#[verifier::opaque]
pub open spec fn process_pci_function_ownership_wf(root_table: IommuRootTable, prc_mp: ProcessLockedMap) -> bool {
    &&& root_table.wf()
    // Root table -> process reverse set.
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        pci_bdf_valid(bus, device, function) ==> {
            let prc_ptr = root_table.spec_index_owner(bus, device, function);
            &&& prc_mp.dom().contains(prc_ptr)
            &&& prc_mp.spec_index(prc_ptr).view_ghost().owned_pci_functions.view().contains((bus, device, function))
        }
    // Process reverse set -> root table.
    &&& forall|p: RwLockProcessPtr, bdf: PciBdf|
        #![trigger prc_mp.spec_index(p).view_ghost().owned_pci_functions.view().contains(bdf)]
        prc_mp.dom().contains(p) && prc_mp.spec_index(p).view_ghost().owned_pci_functions.view().contains(bdf) ==> {
            &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
            &&& root_table.spec_index_owner(bdf.0, bdf.1, bdf.2) == p
        }
}

/// Both directions of `process_pci_function_ownership_wf` at function `bdf` and process `prc_ptr`.
pub proof fn process_pci_function_ownership_wf_at(root_table: IommuRootTable, prc_mp: ProcessLockedMap, bdf: PciBdf, prc_ptr: RwLockProcessPtr)
    requires process_pci_function_ownership_wf(root_table, prc_mp),
    ensures
        pci_bdf_valid(bdf.0, bdf.1, bdf.2) ==> ({
            let owner = root_table.spec_index_owner(bdf.0, bdf.1, bdf.2);
            &&& prc_mp.dom().contains(owner)
            &&& prc_mp.spec_index(owner).view_ghost().owned_pci_functions.view().contains(bdf)
        }),
        prc_mp.dom().contains(prc_ptr) && prc_mp.spec_index(prc_ptr).view_ghost().owned_pci_functions.view().contains(bdf) ==> {
            &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
            &&& root_table.spec_index_owner(bdf.0, bdf.1, bdf.2) == prc_ptr
        },
{ reveal(process_pci_function_ownership_wf); }
}
