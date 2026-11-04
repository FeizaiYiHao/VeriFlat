use vstd::prelude::*;
use crate::*;
verus! {
/// Processes and page tables name each other.
#[verifier::opaque]
pub open spec fn process_pagetable_wf(prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap) -> bool {
    // Process -> page table; the read-only `pagetable`, `pcid`, and `cr3` copies match.
    &&& forall|p: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p).view()]
        prc_mp.dom().contains(p) ==> {
            let process = prc_mp.spec_index(p);
            let table = pt_mp.spec_index(process.view().pagetable).view();
            &&& pt_mp.dom().contains(process.view().pagetable)
            &&& process.view_rodata().view().pagetable == process.view().pagetable
            &&& process.view_rodata().view().pcid == process.view().pcid
            &&& process.view_rodata().view().cr3 == table.cr3
            &&& table.proc_ptr == p
            &&& table.pcid_value() == process.view().pcid
        }
    // Page table -> process.
    &&& forall|pt: RwLockPageTableRoot|
        #![trigger pt_mp.spec_index(pt).view().proc_ptr]
        pt_mp.dom().contains(pt)
            ==>
            prc_mp.dom().contains(pt_mp.spec_index(pt).view().proc_ptr)
            && prc_mp.spec_index(pt_mp.spec_index(pt).view().proc_ptr).view().pagetable == pt
}

pub proof fn process_pagetable_wf_process_at(prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_pagetable_wf(prc_mp, pt_mp),
    ensures
        prc_mp.dom().contains(prc_ptr) ==> ({
            let process = prc_mp.spec_index(prc_ptr);
            let table = pt_mp.spec_index(process.view().pagetable).view();
            &&& pt_mp.dom().contains(process.view().pagetable)
            &&& process.view_rodata().view().pagetable == process.view().pagetable
            &&& process.view_rodata().view().pcid == process.view().pcid
            &&& process.view_rodata().view().cr3 == table.cr3
            &&& table.proc_ptr == prc_ptr
            &&& table.pcid_value() == process.view().pcid
        }),
{ reveal(process_pagetable_wf); }

pub proof fn process_pagetable_wf_pagetable_at(prc_mp: ProcessLockedMap, pt_mp: PageTableLockedMap, pt_ptr: RwLockPageTableRoot)
    requires
        process_pagetable_wf(prc_mp, pt_mp),
    ensures
        pt_mp.dom().contains(pt_ptr) ==> ({
            &&& prc_mp.dom().contains(pt_mp.spec_index(pt_ptr).view().proc_ptr)
            &&& prc_mp.spec_index(pt_mp.spec_index(pt_ptr).view().proc_ptr).view().pagetable == pt_ptr
        }),
{ reveal(process_pagetable_wf); }
}
