use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use crate::locks::*;

verus! {

#[derive(Clone,Copy)]
pub struct KillerInfo{
    pub container: RwLockContainerPtr,
    pub container_depth: usize,

    pub process: RwLockProcessPtr,
    pub process_depth: usize,

    pub thread: RwLockThreadPtr,

    pub cpu_id: CpuId,
}

pub struct RwLockInner{
    lock: AtomicBool, // false means no one is read/writing the lock content.
    writing: bool,
    num_of_reader: usize, // right now we don't need to worry about overflow because we don't support kernel interrupt.

    killer_info: Option<KillerInfo>,
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
    pub fn try_wlock(&mut self) -> Result<(),KillerInfo> {
        loop {
            self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if self.killer_info.is_some() {
                let ret = self.killer_info.unwrap();
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
    pub fn try_wlock_and_mark_kill(&mut self, killer_info: KillerInfo) -> Result<(),KillerInfo> {
        loop {
            self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if self.killer_info.is_some() {
                let ret = self.killer_info.unwrap();
                self.lock.store(false, Ordering::Release);
                return Err(ret);
            }
            if self.num_of_reader == 0 && self.writing == false{
                self.writing = true;
                self.killer_info = Some(killer_info);
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
    pub fn try_rlock(&mut self) -> Result<(),KillerInfo> {
        loop {
            self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if self.killer_info.is_some() {
                let ret = self.killer_info.unwrap();
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

pub open spec fn write_locked_by_same_thread<X:LockMajorTrait, Y:LockMajorTrait, const HasKillStateX: bool, const HasKillStateY: bool>(x: RwLock<X, HasKillStateX>, y: RwLock<Y, HasKillStateY>) -> bool{
    &&&
    x.locking_thread() is Write
    &&&
    y.locking_thread() is Write
    &&&
    x.locking_thread()->Write_thread_id == y.locking_thread()->Write_thread_id
    // false
}

pub open spec fn write_locked_by_same_thread_xyz<X:LockMajorTrait, Y:LockMajorTrait, Z:LockMajorTrait, const HasKillStateX: bool, const HasKillStateY: bool, const HasKillStateZ: bool>
        (x: RwLock<X, HasKillStateX>, y: RwLock<Y, HasKillStateY>, z: RwLock<Z, HasKillStateZ>) -> bool{
    &&&
    x.locking_thread() is Write
    &&&
    y.locking_thread() is Write
    &&&
    z.locking_thread() is Write
    &&&
    x.locking_thread()->Write_thread_id == y.locking_thread()->Write_thread_id
    &&&
    y.locking_thread()->Write_thread_id == z.locking_thread()->Write_thread_id
}

impl<T, const HasKillState: bool> RwLock<T, HasKillState>{
    pub closed spec fn locking_thread(&self) -> RwLockState
    {
        self.locking_thread@
    }
    pub open spec fn locked(&self) -> bool{
        |||
        self.rlocked()
        |||
        self.wlocked()
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
    pub open spec fn read_lock_perm_match(&self, lock_perm:&LockPerm) -> bool {
        &&&
        self.locking_thread() is Read
        &&&
        self.locking_thread()->Read_reader_map.dom().contains(lock_perm.thread_id())
        &&&
        self.locking_thread()->Read_reader_map.spec_index(lock_perm.thread_id()) == lock_perm.lock_id()
    }
    pub open spec fn write_lock_perm_match(&self, lock_perm:&LockPerm) -> bool {
        &&&
        self.locking_thread() is Write
        &&&
        self.locking_thread()->Write_thread_id == lock_perm.thread_id()
        &&&
        self.locking_thread()->Write_lock_id == lock_perm.lock_id()
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
    pub closed spec fn killer_info_inner(&self) -> Option<KillerInfo>{
        self.lock.killer_info
    }
    pub open spec fn killer_info(&self) ->  Option<KillerInfo>{
        if HasKillState{
            self.killer_info_inner()
        }else{
            None
        }
    }
    pub open spec fn being_killed(&self) -> bool{
        if HasKillState{
            self.killer_info_inner() is Some
        }else{
            false
        }
    }
    pub open spec fn being_killed_by(&self, lctx:&LocalContext) -> bool{
        &&&
        self.killer_info_inner() is Some
        &&&
        self.killer_info_inner().unwrap().cpu_id == lctx.thread_id()
    }
    pub closed spec fn is_init(&self) -> bool {
        self.is_init@
    }

    pub closed spec fn view(&self) -> T
    {
        self.value
    }

}

impl<T: LockRecursivelyLockedTrait, const HasKillState: bool> RwLock<T, HasKillState>{
    pub open spec fn partial_locked_by(&self, lctx:&LocalContext) -> bool{
        self.view().partial_locked_by(lctx)
    }    
    pub open spec fn total_locked_by(&self, lctx:&LocalContext) -> bool{
        self.view().total_locked_by(lctx)
    }
}

impl<T:LockInvTrait, const HasKillState: bool> RwLock<T, HasKillState>{
    pub open spec fn inv(&self) -> bool{
        &&&
        self@.inv()
        &&&
        self.is_init()
    }
}

impl<T> RwLock<T, NO_KILL_STATE>{
    #[verifier::external_body]
        pub fn wlock_external(&mut self, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret:Tracked<LockPerm>)
        requires
            true == false, // this function can only be called in the TCB
    {
        self.lock.wlock();
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock_external(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>)
        requires
            true == false, // this function can only be called in the TCB
    {
        self.lock.wunlock();
    }
}
impl<T, const HasKillState: bool> RwLock<T, HasKillState>{
    #[verifier::external_body]
    pub fn take(&mut self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>) -> (ret:T)
        requires
            old(self).wlocked_by(lctx),
            old(self).is_init() == true,

            lp@.state() is WriteLock,
            lp@.thread_id() == lctx.thread_id(),
            lp@.lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            take_ensures(*old(self), *self),
            ret == old(self).view(),
    {
        unsafe { core::ptr::read(&self.value as *const T) }
    }

    #[verifier::external_body]
    pub fn put(&mut self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>, v: T)
        requires
            old(self).wlocked_by(lctx),

            lp@.state() is WriteLock,
            lp@.thread_id() == lctx.thread_id(),
            lp@.lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            put_ensures(*old(self), *self, v),
    {
        unsafe { core::ptr::write(&mut self.value as *mut T, v) }
    }
    #[verifier::external_body]
    pub fn borrow<'a,>(&self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.locked_by(lctx), 
            self.is_init() == true,
            lp@.thread_id() == lctx.thread_id(),

            lp@.state() is WriteLock ==> self.write_lock_perm_match(lp@),
            lp@.state() is ReadLock ==> self.read_lock_perm_match(lp@), 
    {
        unsafe{
            &*(&self.value as *const T)
        }
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait + LockUserVisibilityTrait> RwLock<T,NO_KILL_STATE>{
    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret:Tracked<LockPerm>)
        requires
            old(self)@.container_depth() == lock_id@.container,
            old(self)@.process_depth() == lock_id@.process,
            old(self)@.lock_major_sat(lock_id@.major),
            old(self)@.lock_minor() == lock_id@.minor,

            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id@),
        ensures
            wlock_ensures(*old(self), *self, lock_id@, lctx.thread_id(), ret@),
            lock_ensures(old(lctx), lctx, self.view(), lock_id@),
    {
        self.lock.wlock();
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>)
        requires
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),

            lp@.state() is WriteLock,
            lp@.thread_id() == old(lctx).thread_id(),
            lp@.lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            wunlock_ensures(*old(self), *self),
            unlock_ensures(old(lctx), lctx, self.view(), lp@.lock_id()),
    {
        self.lock.wunlock();
    }

}
pub open spec fn wlock_requires<T: LockUserVisibilityTrait, const HasKillState: bool>(old:RwLock<T, HasKillState>, lctx: &LocalContext) -> bool{
    &&&
    old.locked_by(lctx) == false
    &&&
    lctx.kernel_view_locking_state() is Acquire
    &&&
    old.view().is_user_visible() ==> lctx.user_view_locking_state() is Acquire
}

pub open spec fn wlock_ensures<T:LockInvTrait + LockMajorTrait + LockUserVisibilityTrait, const HasKillState: bool>(old:RwLock<T, HasKillState>, new:RwLock<T, HasKillState>, lock_id: LockId, thread_id: LockThreadId, lock_perm:LockPerm) -> bool{
    &&&
    new.locking_thread() == RwLockState::Write { thread_id: thread_id, lock_id: lock_id }
    &&&
    new.inv()
    &&&
    new@ == old@    
    &&&
    old.locked() == false

    &&&
    lock_perm.state() is WriteLock
    &&&
    lock_perm.lock_id() == lock_id
    &&&
    lock_perm.thread_id() == thread_id
}

pub open spec fn wunlock_ensures<T:LockInvTrait + LockUserVisibilityTrait, const HasKillState: bool>(old:RwLock<T, HasKillState>, new:RwLock<T, HasKillState>) -> bool{
    &&&
    new.locking_thread() == RwLockState::None
    &&&
    new.inv()
    &&&
    new@ == old@
}

pub open spec fn take_ensures<T, const HasKillState: bool>(old:RwLock<T, HasKillState>, new:RwLock<T, HasKillState>) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == false
    &&&
    new@ == old@
}

pub open spec fn put_ensures<T, const HasKillState: bool>(old:RwLock<T, HasKillState>, new:RwLock<T, HasKillState>, v:T) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == true
    &&&
    new@ == v
}

}
