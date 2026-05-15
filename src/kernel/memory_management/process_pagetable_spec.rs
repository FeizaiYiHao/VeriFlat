use vstd::prelude::*;
use crate::*;
verus! {

pub proof fn process_pagetable_match_proof()
    ensures
        forall|process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>, pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>|
            process_pagetable_match_inner(process_map, pagetable_map) <==> process_pagetable_match(process_map, pagetable_map)
{}
pub closed spec fn process_pagetable_match(process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>, pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>) -> bool {
    process_pagetable_match_inner(process_map, pagetable_map)
}

pub open spec fn process_pagetable_match_inner(process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>, pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), PAGE_TABLE_HAS_KILL_STATE>) -> bool {
{
    &&&
    forall|proc_ptr:RwLockProcessPtr|
        #![trigger process_map.spec_index(proc_ptr).view().pagetable]
        process_map.dom().contains(proc_ptr) 
        ==>
        pagetable_map.dom().contains(process_map.spec_index(proc_ptr).view().pagetable)
        &&
        pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().proc_ptr == proc_ptr
        &&
        pagetable_map.spec_index(process_map.spec_index(proc_ptr).view().pagetable).view().pcid_or_ioid() == process_map.spec_index(proc_ptr).view().pcid
            
        
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
}