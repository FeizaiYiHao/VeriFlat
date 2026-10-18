use vstd::prelude::*;

verus! {
use crate::*;

/// Bidirectional ownership index between the static BDF metadata table and
/// each process's lock-free ghost reverse set.  Both directions change only
/// under the root-table lock.
#[verifier::opaque]
pub open spec fn process_pci_function_ownership_wf(root_table: IommuRootTable, process_map: ProcessLockedMap) -> bool {
    &&& root_table.wf()
    // Root table -> process reverse set.
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        pci_bdf_valid(bus, device, function) ==> {
            let proc_ptr = root_table.spec_index_owner(bus, device, function);
            &&& process_map.dom().contains(proc_ptr)
            &&& process_map.spec_index(proc_ptr).view_ghost().owned_pci_functions.view().contains((bus, device, function))
        }
    // Process reverse set -> root table.
    &&& forall|proc_ptr: RwLockProcessPtr, bdf: PciBdf|
        #![trigger process_map.spec_index(proc_ptr).view_ghost().owned_pci_functions.view().contains(bdf)]
        process_map.dom().contains(proc_ptr) && process_map.spec_index(proc_ptr).view_ghost().owned_pci_functions.view().contains(bdf) ==> pci_bdf_valid(bdf.0, bdf.1, bdf.2) && root_table.spec_index_owner(bdf.0, bdf.1, bdf.2) == proc_ptr
}

/// Both directions of `process_pci_function_ownership_wf` at function `bdf` and process `proc_ptr`.
pub proof fn process_pci_function_ownership_wf_at(root_table: IommuRootTable, process_map: ProcessLockedMap, bdf: PciBdf, proc_ptr: RwLockProcessPtr)
    requires process_pci_function_ownership_wf(root_table, process_map),
    ensures
        pci_bdf_valid(bdf.0, bdf.1, bdf.2) ==> ({
            let owner = root_table.spec_index_owner(bdf.0, bdf.1, bdf.2);
            &&& process_map.dom().contains(owner)
            &&& process_map.spec_index(owner).view_ghost().owned_pci_functions.view().contains(bdf)
        }),
        process_map.dom().contains(proc_ptr) && process_map.spec_index(proc_ptr).view_ghost().owned_pci_functions.view().contains(bdf) ==> {
            &&& pci_bdf_valid(bdf.0, bdf.1, bdf.2)
            &&& root_table.spec_index_owner(bdf.0, bdf.1, bdf.2) == proc_ptr
        },
{ reveal(process_pci_function_ownership_wf); }
}
