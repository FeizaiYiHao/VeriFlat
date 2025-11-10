use vstd::prelude::*;
use crate::define::*;
use core::sync::atomic::*;
use std::thread::ThreadId;

use super::LockManager;
verus! {

pub trait LockMinorIdTrait {
    spec fn lock_minor(&self) -> LockMinorId;
}
    
pub trait RwLockTrait {
    spec fn rlocked(&self, thread_id:LockThreadId) -> bool; 
    spec fn wlocked(&self, thread_id:LockThreadId) -> bool; 
    spec fn locked(&self, thread_id:LockThreadId) -> bool;
}

// impl<T> RwLockTrait for T {
//     uninterp spec fn rlocked(&self, thread_id:LockThreadId) -> bool; 
//     uninterp spec fn wlocked(&self, thread_id:LockThreadId) -> bool; 
//     open spec fn locked(&self, thread_id:LockThreadId) -> bool{
//         self.rlocked(thread_id) || self.wlocked(thread_id)
//     } 
// }

pub struct RwLockOption<T, const LMId: LockMajorId>{
    value: Option<T>,
}

impl<T, const LMId: LockMajorId> RwLockTrait for RwLockOption<T, LMId> {
    uninterp spec fn rlocked(&self, thread_id:LockThreadId) -> bool; 
    uninterp spec fn wlocked(&self, thread_id:LockThreadId) -> bool; 
    open spec fn locked(&self, thread_id:LockThreadId) -> bool{
        self.rlocked(thread_id) || self.wlocked(thread_id)
    } 
}

impl<T, const LMId: LockMajorId> RwLockOption<T, LMId>{
    pub uninterp spec fn lock_minor(&self) -> usize;

    pub closed spec fn view(&self) -> Option<T>
    {
        self.value
    }

    pub open spec fn lock_id(&self) -> LockId
    {
        LockId{
            major: LMId,
            minor: self.lock_minor(),
        }
    }

    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lm): Tracked<&mut LockManager>) -> (ret:Tracked<LockPerm>)
            requires
            old(self).locked(old(lm).thread_id()) == false,
            old(lm).lock_seq().len() == 0 ||
                old(self).lock_id().greater(&old(lm).lock_seq().last()),
        ensures
            self.rlocked(lm.thread_id()) == false,
            self.wlocked(lm.thread_id()),
            self.lock_id() == old(self).lock_id(),
            self.view() == old(self).view(),
            lm.thread_id() == old(lm).thread_id(),
            lm.lock_seq() == old(lm).lock_seq().push(self.lock_id()),
            ret@.local_thread_id == lm.thread_id(),
            ret@.state == LockState::WriteLock,
            ret@.lock_id() == self.lock_id()
    {
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lm): Tracked<&mut LockManager>, lp: Tracked<LockPerm>)
        requires
            old(self).locked(old(lm).thread_id()),
            lp@.local_thread_id == old(lm).thread_id(),
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self).lock_id(),
        ensures
            self.rlocked(lm.thread_id()) == false,
            self.wlocked(lm.thread_id()) == false,
            self.lock_id() == old(self).lock_id(),
            self.view() == old(self).view(),
            lm.thread_id() == old(lm).thread_id(),
            lm.lock_seq() == old(lm).lock_seq().remove_value(self.lock_id()),
    {}

    #[verifier::external_body]
    pub fn take(&mut self, lp: Tracked<&LockPerm>) -> (ret: Option<T>)
        requires
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self).lock_id(),
        ensures
            forall|i:usize|
                #![auto] 
                self.rlocked(i) == old(self).rlocked(i),
            forall|i:usize|
                #![auto] 
                self.wlocked(i) == old(self).wlocked(i),
            self.lock_id() == old(self).lock_id(),
            self.view() is None,
            ret == old(self).view()
    {
        self.value.take()
    }

    #[verifier::external_body]
    pub fn set(&mut self, lp: Tracked<&LockPerm>, v: Option<T>)
        requires
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self).lock_id(),
        ensures
            forall|i:usize|
                #![auto] 
                self.rlocked(i) == old(self).rlocked(i),
            forall|i:usize|
                #![auto] 
                self.wlocked(i) == old(self).wlocked(i),
            self.lock_id() == old(self).lock_id(),
            self.view() == v,
    {
        self.value = v;
    }
}

pub struct RwLock<T, const LMId: LockMajorId>{
    value: T,
}

impl<T, const LMId: LockMajorId> RwLockTrait for RwLock<T, LMId> {
    uninterp spec fn rlocked(&self, thread_id:LockThreadId) -> bool; 
    uninterp spec fn wlocked(&self, thread_id:LockThreadId) -> bool; 
    open spec fn locked(&self, thread_id:LockThreadId) -> bool{
        self.rlocked(thread_id) || self.wlocked(thread_id)
    } 
}

impl<T:Copy, const LMId: LockMajorId> RwLock<T, LMId>{
    pub uninterp spec fn lock_minor(&self) -> usize;

    pub closed spec fn view(&self) -> T
    {
        self.value
    }

    pub open spec fn lock_id(&self) -> LockId
    {
        LockId{
            major: LMId,
            minor: self.lock_minor(),
        }
    }

    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lm): Tracked<&mut LockManager>) -> (ret:Tracked<LockPerm>)
            requires
            old(self).locked(old(lm).thread_id()) == false,
            old(lm).lock_seq().len() == 0 ||
                old(self).lock_id().greater(&old(lm).lock_seq().last()),
        ensures
            self.rlocked(lm.thread_id()) == false,
            self.wlocked(lm.thread_id()),
            self.lock_id() == old(self).lock_id(),
            self.view() == old(self).view(),
            lm.thread_id() == old(lm).thread_id(),
            lm.lock_seq() == old(lm).lock_seq().push(self.lock_id()),
            ret@.local_thread_id == lm.thread_id(),
            ret@.state == LockState::WriteLock,
            ret@.lock_id() == self.lock_id()
    {
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lm): Tracked<&mut LockManager>, lp: Tracked<LockPerm>)
        requires
            old(self).locked(old(lm).thread_id()),
            lp@.local_thread_id == old(lm).thread_id(),
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self).lock_id(),
        ensures
            self.rlocked(lm.thread_id()) == false,
            self.wlocked(lm.thread_id()) == false,
            self.lock_id() == old(self).lock_id(),
            self.view() == old(self).view(),
            lm.thread_id() == old(lm).thread_id(),
            lm.lock_seq() == old(lm).lock_seq().remove_value(self.lock_id()),
    {}

    #[verifier::external_body]
    pub fn take(&mut self, lp: Tracked<&LockPerm>) -> (ret: T)
        requires
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self).lock_id(),
        ensures
            forall|i:usize|
                #![auto] 
                self.rlocked(i) == old(self).rlocked(i),
            forall|i:usize|
                #![auto] 
                self.wlocked(i) == old(self).wlocked(i),
            self.lock_id() == old(self).lock_id(),
            old(self).view() == self.view(),
            ret == old(self).view()
    {
        self.value
    }

    #[verifier::external_body]
    pub fn set(&mut self, lp: Tracked<&LockPerm>, v: T)
        requires
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self).lock_id(),
        ensures
            forall|i:usize|
                #![auto]
                self.rlocked(i) == old(self).rlocked(i),
            forall|i:usize|
                #![auto]
                self.wlocked(i) == old(self).wlocked(i),
            self.lock_id() == old(self).lock_id(),
            self.view() == v,
    {
        self.value = v;
    }
}

pub tracked enum LockState {
    Mutex,
    ReadLock,
    WriteLock,
}

pub tracked struct LockPerm {
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

