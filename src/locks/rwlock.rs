use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use crate::locks::*;

verus! {

pub trait LockMinorIdTrait {
    spec fn lock_minor(&self) -> LockMinorId;
}

pub struct RwLock<T>{
    value: T,

    is_init: Ghost<bool>,
    released: Ghost<bool>,
    modified: Ghost<bool>,
    reading_thread: Ghost<Map<LockThreadId, LockId>>,
    writing_thread: Ghost<Option<LockThreadId>>,
}

pub open spec fn write_locked_by_same_thread<T:LockedUtil, V:LockedUtil>(x: RwLock<T>, y: RwLock<V>) -> bool{
    &&&
    x.writing_thread() is Some
    &&&
    y.writing_thread() is Some
    &&&
    x.writing_thread()->0 == y.writing_thread()->0
}

impl<T:LockedUtil> RwLock<T>{
    pub closed spec fn reading_thread(&self) -> Set<LockThreadId>{
        self.reading_thread@
    } 
    pub closed spec fn writing_thread(&self) -> Option<LockThreadId>{
        self.writing_thread@
    } 
    pub open spec fn rlocked_by(&self, thread_id:LockThreadId) -> bool{
        self.reading_thread().contains(thread_id)
    } 
    pub open  spec fn wlocked_by(&self, thread_id:LockThreadId) -> bool{
        &&&
        self.writing_thread() is Some
        &&&
        self.writing_thread()->0 == thread_id
    }
    pub open spec fn rlocked(&self) -> bool{
        self.reading_thread().len() != 0
    }
    pub open spec fn wlocked(&self) -> bool{
        self.writing_thread() is Some
    }
    pub open spec fn locked(&self, thread_id:LockThreadId) -> bool{
        self.rlocked_by(thread_id) || self.wlocked_by(thread_id)
    } 


    pub open spec fn inv(&self) -> bool{
        &&&
        self.is_init()
        &&&
        self@.inv()
    }

    pub closed spec fn is_init(&self) -> bool{
        self.is_init@
    }


    /// re-aquiring a released lock will make the state of the object well-formed bu unkown.  
    pub closed spec fn released(&self) -> bool{
        self.released@
    }

    /// 
    pub closed spec fn modified(&self) -> bool{
        self.modified@
    }

    pub closed spec fn view(&self) -> T
        recommends 
            self.is_init(),
    {
        self.value
    }

    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lock_manager): Tracked<&mut LockManager>) -> (ret:Tracked<LockPerm>)
        requires
            old(self).locked(old(lock_manager).thread_id()) == false,

            old(lock_manager).lock_seq().len() == 0 ||
                old(self).lock_id().greater(old(lock_manager).lock_seq().last()),
        ensures
            self.rlocked_by(lock_manager.thread_id()) == false,
            self.wlocked_by(lock_manager.thread_id()),
            self.lock_id() == old(self).lock_id(),
            old(self).released() == false ==> self.view() == old(self).view(),
            self@.inv(),
            old(self).is_init(),
            self.is_init() == old(self).is_init(),

            lock_manager.thread_id() == old(lock_manager).thread_id(),
            lock_manager.lock_seq() == old(lock_manager).lock_seq().push(self.lock_id()),
            old(lock_manager).wf() ==> lock_manager.wf(),
            ret@.thread_id() == lock_manager.thread_id(),

            ret@.state == LockState::WriteLock,
            ret@.lock_id() == self.lock_id(),

            self.modified() == false,
    {
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lock_manager): Tracked<&mut LockManager>, lp: Tracked<LockPerm>)
        requires
            old(self).locked(old(lock_manager).thread_id()),
            old(self).inv(),

            lp@.thread_id() == old(lock_manager).thread_id(),
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self).lock_id(),

            old(lock_manager).lock_seq().contains(old(self).lock_id())
        ensures
            self.rlocked_by(lock_manager.thread_id()) == false,
            self.wlocked_by(lock_manager.thread_id()) == false,
            self.lock_id() == old(self).lock_id(),
            self.inv(),
            self.view() == old(self).view(),
            self.is_init() == old(self).is_init(),

            lock_manager.thread_id() == old(lock_manager).thread_id(),
            lock_manager.lock_seq() === old(lock_manager).lock_seq().remove_value(self.lock_id()),
            old(lock_manager).wf() ==> lock_manager.wf(),

            self.released(),
    {}
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

    pub open spec fn thread_id(&self) -> LockThreadId{
        self.local_thread_id
    }
}

}
