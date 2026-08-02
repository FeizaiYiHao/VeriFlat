use vstd::prelude::*;

verus! {

use crate::*;

/// Bidirectional ownership index between the static BDF metadata table and
/// each process's reverse set.  The process-local counter is tied to the set
/// length by `Process::pci_function_ownership_wf`.
#[verifier::opaque]
pub open spec fn process_pci_function_ownership_wf(
    root_table: &IommuRootTable,
    process_map: ProcessLockedMap,
) -> bool {
    &&& root_table.wf()
    // Root table -> process reverse set.
    &&& forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        pci_bdf_valid(bus, device, function)
        ==>
        {
            let proc_ptr = root_table.spec_index_owner(bus, device, function);
            &&& process_map.dom().contains(proc_ptr)
            &&& process_map.spec_index(proc_ptr).view()
                .owned_pci_functions.view().contains((bus, device, function))
        }
    // Process reverse set -> root table.
    &&& forall|proc_ptr: RwLockProcessPtr, bdf: PciBdf|
        #![trigger process_map.spec_index(proc_ptr).view()
            .owned_pci_functions.view().contains(bdf)]
        process_map.dom().contains(proc_ptr)
        && process_map.spec_index(proc_ptr).view()
            .owned_pci_functions.view().contains(bdf)
        ==>
        pci_bdf_valid(bdf.0, bdf.1, bdf.2)
        && root_table.spec_index_owner(bdf.0, bdf.1, bdf.2) == proc_ptr
}

/// This is the deletion-path payoff of the reverse index: a zero process-local
/// counter proves that no static root-table entry names the process, without a
/// runtime scan of all 65,536 BDF slots.
pub proof fn zero_pci_function_ref_counter_implies_no_root_ownership(
    root_table: &IommuRootTable,
    process_map: ProcessLockedMap,
    proc_ptr: RwLockProcessPtr,
)
    requires
        process_perms_wf(process_map),
        process_pci_function_ownership_wf(root_table, process_map),
        process_map.dom().contains(proc_ptr),
        process_map.spec_index(proc_ptr).view().pci_function_ref_counter == 0,
    ensures
        forall|bus: usize, device: usize, function: usize|
            #![trigger root_table.spec_index_owner(bus, device, function)]
            pci_bdf_valid(bus, device, function)
            ==> root_table.spec_index_owner(bus, device, function) != proc_ptr,
{
    assert forall|bus: usize, device: usize, function: usize|
        #![trigger root_table.spec_index_owner(bus, device, function)]
        pci_bdf_valid(bus, device, function)
        implies root_table.spec_index_owner(bus, device, function) != proc_ptr
    by {
        reveal(process_perms_wf);
        reveal(process_pci_function_ownership_wf);
        if root_table.spec_index_owner(bus, device, function) == proc_ptr {
            let owned = process_map.spec_index(proc_ptr).view()
                .owned_pci_functions.view();
            vstd::set::lemma_set_contains_len(
                owned,
                (bus, device, function),
            );
        }
    };
}

}
