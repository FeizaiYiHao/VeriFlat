use vstd::prelude::*;
use crate::*;
verus! {

#[verifier::opaque]
pub open spec fn process_pagetable_match(process_map: ProcessLockedMap, pagetable_map: PageTableLockedMap) -> bool {
    &&&
    forall|proc_ptr:RwLockProcessPtr|
        #![trigger process_map.spec_index(proc_ptr).view().pagetable]
        process_map.dom().contains(proc_ptr) 
        ==>
        pagetable_map.dom().contains(process_map.spec_index(proc_ptr).view().pagetable)
        &&
        pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().proc_ptr == proc_ptr
        &&
        pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().pcid_value() == process_map.spec_index(proc_ptr).view().pcid
            
        
    &&&
    forall|pt_ptr:RwLockPageTableRoot|
        #![trigger pagetable_map.spec_index(pt_ptr).view().proc_ptr]
        pagetable_map.dom().contains(pt_ptr)
        ==>
        process_map.dom().contains(pagetable_map.spec_index(pt_ptr).view().proc_ptr)
        &&
        process_map.spec_index(pagetable_map.spec_index(pt_ptr).view().proc_ptr).view().pagetable == pt_ptr

}

}
