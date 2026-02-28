use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use crate::locks::*;

verus! {

pub struct RwLockInner{
    lock: AtomicBool, // false means no one is read/writing the lock content.
    writing: bool,
    pub kill: Option<LockThreadId>, // The id of the CPU that has marked this object as being killed
    num_of_reader: usize, // right now we don't need to worry about overflow because we don't support kernel naterrupt.
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
    pub fn try_wlock(&mut self) -> Result<(),LockThreadId> {
        loop {
            self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if self.kill.is_some() {
                let ret = self.kill.unwrap();
                self.lock.store(false, Ordering::Release);
                return Err(ret);
            }
            if self.num_of_reader == 0 && self.writing == false{
                self.writing = true;
                self.lock.store(false, Ordering::Release);
                return Ok(());
            }
            self.lock.store(false, Ordering::Release);
        }
    }

    #[verifier::external_body]
    pub fn try_wlock_and_mark_kill(&mut self, thread_id: LockThreadId) -> Result<(),LockThreadId> {
        loop {
            self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if self.kill.is_some() {
                let ret = self.kill.unwrap();
                self.lock.store(false, Ordering::Release);
                return Err(ret);
            }
            if self.num_of_reader == 0 && self.writing == false{
                self.writing = true;
                self.kill = Some(thread_id);
                self.lock.store(false, Ordering::Release);
                return Ok(());
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
    pub fn try_rlock(&mut self) -> Result<(),LockThreadId> {
        loop {
            self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if self.kill.is_some() {
                let ret = self.kill.unwrap();
                self.lock.store(false, Ordering::Release);
                return Err(ret);
            }
            if self.writing == false{
                self.num_of_reader = self.num_of_reader + 1;
                self.lock.store(false, Ordering::Release);
                return Ok(());
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

pub enum RwLockState{
    Write{thread_id: LockThreadId, lock_id: LockId},
    Read{reader_map: Map<LockThreadId, LockId>},
    None,
}

pub struct RwLock<T, const HasKillState: bool>{
    lock: RwLockInner,
    value: T,

    is_init: Ghost<bool>,
    serial_num: Ghost<nat>,
    modified: Ghost<bool>,
    locking_thread: Ghost<RwLockState>,
}

pub open spec fn write_locked_by_same_thread<T:LockedUtil, V:LockedUtil, const HasKillStateX: bool, const HasKillStateY: bool>(x: RwLock<T, HasKillStateX>, y: RwLock<V, HasKillStateY>) -> bool{
    &&&
    x.locking_thread() is Write
    &&&
    y.locking_thread() is Write
    &&&
    x.locking_thread()->Write_thread_id == y.locking_thread()->Write_thread_id
}

impl<T, const HasKillState: bool> RwLock<T, HasKillState>{
    pub closed spec fn locking_thread(&self) -> RwLockState
    {
        self.locking_thread@
    }
    pub open spec fn rlocked(&self) -> bool{
        &&&
        self.locking_thread() is Read
    } 
    pub open spec fn rlocked_by(&self, lctx:&LocalContext) -> bool{
        &&&
        self.locking_thread() is Read
        &&&
        self.locking_thread()->Read_reader_map.dom().contains(lctx.thread_id())
    } 
    pub open spec fn wlocked(&self) -> bool{
        &&&
        self.locking_thread() is Write
    } 
    pub open spec fn wlocked_by(&self, lctx:&LocalContext) -> bool{
        &&&
        self.locking_thread() is Write
        &&&
        self.locking_thread()->Write_thread_id == lctx.thread_id()
    } 
    pub open spec fn locked_by(&self, lctx:&LocalContext) -> bool{
        |||
        self.rlocked_by(lctx)
        |||
        self.wlocked_by(lctx)
    }
    pub closed spec fn killing_thread_id_inner(&self) -> Option<LockThreadId>{
        self.lock.kill
    }
    pub open spec fn killing_thread_id(&self) ->  Option<LockThreadId>{
        if HasKillState{
            self.killing_thread_id_inner()
        }else{
            None
        }
    }
    pub open spec fn being_killed(&self) -> bool{
        self.killing_thread_id() is Some
    }
    pub open spec fn being_killed_by(&self, lctx:&LocalContext) -> bool{
        self.killing_thread_id() != Some(lctx.thread_id())
    }
    pub closed spec fn is_init(&self) -> bool {
        self.is_init@
    }

    /// 
    pub closed spec fn serial_num(&self) -> nat {
        self.serial_num@
    }

    /// 
    pub closed spec fn modified(&self) -> bool{
        self.modified@
    }

    pub closed spec fn view(&self) -> T
    {
        self.value
    }
}
impl<T:LockedUtil, const HasKillState: bool> RwLock<T,HasKillState>{
    pub open spec fn inv(&self) -> bool{
        &&&
        self@.inv()
        &&&
        self.is_init()
    }

    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_major: Ghost<LockMajorId>) -> (ret:Tracked<LockPerm>)
        requires
            old(self)@.lock_major_sat(lock_major@),

            wlock_requires(*old(self), old(lctx)),
        // ensures
            // TODO fill
    {
        self.lock.wlock();
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>)
        // TODO fill
    {
        self.lock.wunlock();
    }

    #[verifier::external_body]
    pub fn take(&mut self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>) -> T
    {
        unsafe { core::ptr::read(&self.value as *const T) }
    }
    #[verifier::external_body]
    pub fn put(&mut self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>, v: T)
    {
        unsafe { core::ptr::write(&mut self.value as *mut T, v) }
    }
}

pub open spec fn wlock_requires<T:LockedUtil, const HasKillState: bool>(old:RwLock<T, HasKillState>, lctx: &LocalContext) -> bool{
    &&&
    old.locked_by(lctx) == false
    &&&
    old.serial_num() == lctx.locking_serial_num()
}

pub open spec fn wlock_ensures<T:LockedUtil, const HasKillState: bool>(old:RwLock<T, HasKillState>, new:RwLock<T, HasKillState>, lock_id: LockId, thread_id: LockThreadId, lock_perm:LockPerm) -> bool{
    &&&
    new.locking_thread() == RwLockState::Write { thread_id: thread_id, lock_id: lock_id }
    &&&
    new.inv()
    &&&
    new.serial_num() == old.serial_num()
    &&&
    new.modified() == old.modified()
    &&&
    new.being_killed() == old.being_killed()
    &&& 
    new.being_killed() == false
    &&&
    new@ == old@

    &&&
    lock_perm.state() is WriteLock
    &&&
    lock_perm.lock_id() == lock_id
    &&&
    lock_perm.thread_id() == thread_id

    &&&
    new.killing_thread_id_inner() == old.killing_thread_id_inner()
}

pub open spec fn wunlock_ensures<T:LockedUtil, const HasKillState: bool>(old:RwLock<T, HasKillState>, new:RwLock<T, HasKillState>) -> bool{
    &&&
    new.locking_thread() == RwLockState::None
    &&&
    new.inv()
    &&&
    new.modified() == old.modified()
    &&&
    new@ == old@

    &&&
    new.killing_thread_id_inner() == old.killing_thread_id_inner()
}

pub open spec fn take_ensures<T:LockedUtil, const HasKillState: bool>(old:RwLock<T, HasKillState>, new:RwLock<T, HasKillState>) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == false
    &&&
    new.serial_num() == old.serial_num()
    &&&
    new.modified() == old.modified()
    &&&
    new@ == old@

    &&&
    new.killing_thread_id_inner() == old.killing_thread_id_inner()
}

pub open spec fn put_ensures<T:LockedUtil, const HasKillState: bool>(old:RwLock<T, HasKillState>, new:RwLock<T, HasKillState>, v:T) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == true
    &&&
    new.serial_num() == old.serial_num()
    &&&
    new.modified() == old.modified()
    &&&
    new@ == v
    
    &&&
    new.killing_thread_id_inner() == old.killing_thread_id_inner()
}

}
