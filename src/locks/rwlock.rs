use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use crate::locks::*;

verus! {

pub struct RwLockInner{
    lock: AtomicBool, // false means no one is read/writing the lock content.
    writing: bool,
    num_of_reader: usize, // right now we don't need to worry about overflow because we don't support kernel interrupt.
}

impl RwLockInner{
    #[verifier::external_body]
    pub fn wlock(&mut self) {
        loop {
            self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if self.num_of_reader == 0 && self.writing == false{
                self.writing = true;
                self.lock.store(false, Ordering::Release);
                break;
            }
            self.lock.store(false, Ordering::Release);
        }
    }
    #[verifier::external_body]
    pub fn wunlock(&mut self) {
        self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
        self.writing = false;
        self.lock.store(false, Ordering::Release);
        
    }

    #[verifier::external_body]
    pub fn rlock(&mut self) {
        loop {
            self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if self.writing == false{
                self.num_of_reader = self.num_of_reader + 1;
                self.lock.store(false, Ordering::Release);
                break;
            }
            self.lock.store(false, Ordering::Release);
        }
    }
    #[verifier::external_body]
    pub fn runlock(&mut self) {
        self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
        self.num_of_reader = self.num_of_reader - 1;
        self.lock.store(false, Ordering::Release);
    }
}

pub trait LockMinorIdTrait {
    spec fn lock_minor(&self) -> LockMinorId;
}

pub enum LockingThread{
    Write{thread_id: LockThreadId, lock_id: LockId},
    Read{thread_id: LockThreadId, lock_id: LockId},
    None,
}

pub struct RwLock<T>{
    lock: RwLockInner,
    value: T,

    is_init: Ghost<bool>,
    num_released: Ghost<int>,
    modified: Ghost<bool>,
    locking_thread: Ghost<LockingThread>,
}

// pub open spec fn write_locked_by_same_thread<T:LockedUtil, V:LockedUtil>(x: RwLock<T>, y: RwLock<V>) -> bool{
//     &&&
//     x.writing_thread() is Some
//     &&&
//     y.writing_thread() is Some
//     &&&
//     x.writing_thread()->0 == y.writing_thread()->0
// }

impl<T:LockedUtil> RwLock<T>{
    pub closed spec fn locking_thread(&self) -> LockingThread
    {
        self.locking_thread@
    }
    pub open spec fn rlocked_by(&self, thread_id:LockThreadId) -> bool{
        &&&
        self.locking_thread() is Read
        &&&
        self.locking_thread()->Read_thread_id == thread_id
    } 
    pub open spec fn wlocked_by(&self, thread_id:LockThreadId) -> bool{
        &&&
        self.locking_thread() is Write
        &&&
        self.locking_thread()->Write_thread_id == thread_id
    } 
    pub open spec fn lock_id(&self) -> LockId{
        if self.locking_thread() is Read {
            self.locking_thread()->Read_lock_id
        }else if  self.locking_thread() is Write {
            self.locking_thread()->Write_lock_id
        }else{
            arbitrary()
        }
    } 
    pub open spec fn locked_by(&self, thread_id:LockThreadId) -> bool{
        |||
        self.rlocked_by(thread_id)
        |||
        self.wlocked_by(thread_id)
    } 


    pub open spec fn inv(&self) -> bool{
        &&&
        self@.inv()
    }

    pub closed spec fn is_init(&self) -> bool {
        self.is_init@
    }

    /// 
    pub closed spec fn num_released(&self) -> int {
        self.num_released@
    }

    /// 
    pub closed spec fn modified(&self) -> bool{
        self.modified@
    }

    pub closed spec fn view(&self) -> T
    {
        self.value
    }

    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lock_manager): Tracked<&mut LockManager>, lock_major: Ghost<LockMajorId>) -> (ret:Tracked<LockPerm>)
        requires
            // old(self).locked(old(lock_manager).thread_id()) == false,

            // old(self).lock_major_sat(lock_major@),
            // old(lock_manager).lock_seq().len() == 0 ||
            //     lock_major.greater(old(lock_manager).lock_seq().last()),
        ensures
            // self.rlocked_by(lock_manager.thread_id()) == false,
            // self.wlocked_by(lock_manager.thread_id()),

            // self@.inv(),

            // lock_manager.thread_id() == old(lock_manager).thread_id(),
            // lock_manager.lock_seq() == old(lock_manager).lock_seq().push(lock_major),
            // old(lock_manager).wf() ==> lock_manager.wf(),
            // ret@.thread_id() == lock_manager.thread_id(),

            // ret@.state == LockState::WriteLock,
            // ret@.lock_id() == self.lock_id(),

            // self.modified() == false,
    {
        self.lock.wlock();
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lock_manager): Tracked<&mut LockManager>, lp: Tracked<LockPerm>)
        // requires
        //     old(self).locked(old(lock_manager).thread_id()),
        //     old(self).inv(),

        //     lp@.thread_id() == old(lock_manager).thread_id(),
        //     lp@.state == LockState::WriteLock,
        //     lp@.lock_id() == old(self).lock_id(),

        //     old(lock_manager).lock_seq().contains(old(self).lock_id())
        // ensures
        //     self.rlocked_by(lock_manager.thread_id()) == false,
        //     self.wlocked_by(lock_manager.thread_id()) == false,
        //     self.lock_id() == old(self).lock_id(),
        //     self.inv(),
        //     self.view() == old(self).view(),
        //     self.is_init() == old(self).is_init(),

        //     lock_manager.thread_id() == old(lock_manager).thread_id(),
        //     lock_manager.lock_seq() === old(lock_manager).lock_seq().remove_value(self.lock_id()),
        //     old(lock_manager).wf() ==> lock_manager.wf(),

        //     self.released(),
    {
        self.lock.wunlock();
    }
}

}
