use vstd::prelude::*;
use crate::*;
verus! {
#[verifier::opaque]
pub open spec fn process_pagetable_match(process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap) -> bool {
    &&& forall|proc_ptr:RwLockProcessPtr|
        #![trigger process_map.spec_index(proc_ptr).view()]
        process_map.dom().contains(proc_ptr)
            ==> pagetable_map.dom().contains(process_map.spec_index(proc_ptr).view().pagetable)
            && process_map.spec_index(proc_ptr).view_rodata().view().pagetable == process_map.spec_index(proc_ptr).view().pagetable
            && process_map.spec_index(proc_ptr).view_rodata().view().pcid == process_map.spec_index(proc_ptr).view().pcid
            && process_map.spec_index(proc_ptr).view_rodata().view().cr3 == pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().cr3
            && pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().proc_ptr == proc_ptr
            && pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().pcid_value() == process_map.spec_index(proc_ptr).view().pcid
    &&& forall|pt_ptr:RwLockPageTableRoot|
        #![trigger pagetable_map.spec_index(pt_ptr).view().proc_ptr]
        pagetable_map.dom().contains(pt_ptr)
            ==> process_map.dom().contains(pagetable_map.spec_index(pt_ptr).view().proc_ptr)
            && process_map.spec_index(pagetable_map.spec_index(pt_ptr).view().proc_ptr).view().pagetable == pt_ptr
}

pub proof fn process_pagetable_match_process_at(process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, proc_ptr: RwLockProcessPtr)
    requires
        process_pagetable_match(process_map, pagetable_map),
    ensures
        process_map.dom().contains(proc_ptr) ==> ({
            &&& pagetable_map.dom().contains(process_map.spec_index(proc_ptr).view().pagetable)
            &&& process_map.spec_index(proc_ptr).view_rodata().view().pagetable == process_map.spec_index(proc_ptr).view().pagetable
            &&& process_map.spec_index(proc_ptr).view_rodata().view().pcid == process_map.spec_index(proc_ptr).view().pcid
            &&& process_map.spec_index(proc_ptr).view_rodata().view().cr3 == pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().cr3
            &&& pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().proc_ptr == proc_ptr
            &&& pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().pcid_value() == process_map.spec_index(proc_ptr).view().pcid
        }),
{ reveal(process_pagetable_match); }

pub proof fn process_pagetable_match_pagetable_at(process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap, pt_ptr: RwLockPageTableRoot)
    requires
        process_pagetable_match(process_map, pagetable_map),
    ensures
        pagetable_map.dom().contains(pt_ptr) ==> ({
            &&& process_map.dom().contains(pagetable_map.spec_index(pt_ptr).view().proc_ptr)
            &&& process_map.spec_index(pagetable_map.spec_index(pt_ptr).view().proc_ptr).view().pagetable == pt_ptr
        }),
{ reveal(process_pagetable_match); }
}
