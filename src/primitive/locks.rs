use vstd::prelude::*;
use crate::define::*;
use core::sync::atomic::*;
use std::thread::ThreadId;
verus! {

pub trait RwLockTrait{
    spec fn rlocked(&self, thread_id:LockThreadId) -> bool; 
    spec fn wlocked(&self, thread_id:LockThreadId) -> bool; 
}

impl<T> RwLockTrait for T {
    uninterp spec fn rlocked(&self, thread_id:LockThreadId) -> bool; 
    uninterp spec fn wlocked(&self, thread_id:LockThreadId) -> bool; 
}

pub tracked enum LockState {
    Mutex,
    ReadLock,
    WriteLock,
}

pub tracked struct LockPerm{
    pub local_thread_id: LockThreadId,
    pub lock_major: LockMajorId,
    pub lock_minor: LockMinorId,
    pub state: LockState
}

impl LockPerm{
    pub open spec fn lock_id(&self) -> LockId{
        LockId{
            major:self.lock_major,
            minor:self.lock_minor,
        }
    }
}

}

// //private to the kernel
// Page{
//     reference_counter:usize,
//     set: Set<(PageTableID, VAddr)>,
// }

// inv1: if page is unlocked, len(set) == reference_counter,

// Pagetagle{
//     map: Map<VAddr, page>
// }

// inv2: forall| pt in system, forall| (vaddr, page) in pt.map.pairs()
//         page.set.contains((pt.id, vaddr)) || page and pt are locked by the same thread

//     forall| page in system, forall| (pt_id, vaddr) in page.set()
//         system.get_pt(pt_id).map.contains((vaddr, page)) || page and pt are locked by the same thread


// Page -> page A. 

// T1 locks page A,  --> A was previously unlocked. --> len(A.set) == A.reference_counter, --> A.set is empty
// T1 locks no page table. 
// T1 sees that A.reference_counter == 0.
// infer? 
// We can safely free page A.

// mmap()
// {
//     T1 locks page A, 
//     T1 locks pagetable P, 
//     {T1 incerment A.reference_counter + A.set.add(P, VA)} --> check inv2
//     // Break inv2
//     {T1 P.map.add((VA, A))} --> check inv2
//     T1 unlocks P, --> check inv2 /// hard work
//     T1 unlocks A,
//     T1 locks page A, 
//     /// something else
//     T1 unlocks page A,  
// }

