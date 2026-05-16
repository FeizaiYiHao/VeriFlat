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
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok(){
                if self.num_of_reader == 0 && self.writing == false{
                    self.writing = true;
                    self.lock.store(false, Ordering::Release);
                    break;
                }
                self.lock.store(false, Ordering::Release);
            }
        }
    }

    #[verifier::external_body]
    pub fn try_wlock(&mut self) -> Result<(),KillerInfo> {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok(){
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
    }

    #[verifier::external_body]
    pub fn try_wlock_and_mark_kill(&mut self, killer_info: KillerInfo) -> Result<(),KillerInfo> {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok(){
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
    }

    
    #[verifier::external_body]
    pub fn wunlock(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok(){
                self.writing = false;
                self.lock.store(false, Ordering::Release);
                break;
            }
        }
    }

    #[verifier::external_body]
    pub fn rlock(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok(){
                if self.writing == false{
                    self.num_of_reader = self.num_of_reader + 1;
                    self.lock.store(false, Ordering::Release);
                    break;
                    }
                self.lock.store(false, Ordering::Release);  
            }
        }
    }
    #[verifier::external_body]
    pub fn try_rlock(&mut self) -> Result<(),KillerInfo> {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok(){
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
    }
    #[verifier::external_body]
    pub fn runlock(&mut self) {
        loop{
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok(){
                self.num_of_reader = self.num_of_reader - 1;
                self.lock.store(false, Ordering::Release);
                break;
            }
        }

    }
}

pub enum RwLockState{
    Write{thread_id: LockThreadId, lock_id: LockId},
    Read{reader_map: Map<LockThreadId, LockId>},
    None,
}

#[repr(C)]
pub struct RwLock<T, ROT, GhostT, const HAS_KILL_STATE: bool>{
    lock: RwLockInner,
    value: T,
    read_only_value: ROT,
    ghost_value: Ghost<GhostT>,

    is_init: Ghost<bool>,
    serial_num: Ghost<nat>,
    modified: Ghost<bool>,
    locking_thread: Ghost<RwLockState>,
}

// pub open spec fn write_locked_by_same_thread<X:LockMajorTrait, Y:LockMajorTrait, const HAS_KILL_STATEX: bool, const HAS_KILL_STATEY: bool>(x: RwLock<X, HAS_KILL_STATEX>, y: RwLock<Y, HAS_KILL_STATEY>) -> bool{
//     &&&
//     x.locking_thread() is Write
//     &&&
//     y.locking_thread() is Write
//     &&&
//     x.locking_thread()->Write_thread_id == y.locking_thread()->Write_thread_id
//     // false
// }

// pub open spec fn write_locked_by_same_thread_xyz<X:LockMajorTrait, Y:LockMajorTrait, Z:LockMajorTrait, const HAS_KILL_STATEX: bool, const HAS_KILL_STATEY: bool, const HAS_KILL_STATEZ: bool>
//         (x: RwLock<X, HAS_KILL_STATEX>, y: RwLock<Y, HAS_KILL_STATEY>, z: RwLock<Z, HAS_KILL_STATEZ>) -> bool{
//     &&&
//     x.locking_thread() is Write
//     &&&
//     y.locking_thread() is Write
//     &&&
//     z.locking_thread() is Write
//     &&&
//     x.locking_thread()->Write_thread_id == y.locking_thread()->Write_thread_id
//     &&&
//     y.locking_thread()->Write_thread_id == z.locking_thread()->Write_thread_id
// }

impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
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
        if HAS_KILL_STATE{
            self.killer_info_inner()
        }else{
            None
        }
    }
    pub open spec fn being_killed(&self) -> bool{
        if HAS_KILL_STATE{
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

    pub closed spec fn view_rodata(&self) -> ROT
    {
        self.read_only_value
    }

    pub closed spec fn view_ghost_data(&self) -> GhostT
    {
        self.ghost_value.view()
    }

}

impl<T: LockRecursivelyLockedTrait, ROT, GhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
    pub open spec fn partial_locked_by(&self, lctx:&LocalContext) -> bool{
        self.view().partial_locked_by(lctx)
    }    
    pub open spec fn total_locked_by(&self, lctx:&LocalContext) -> bool{
        self.view().total_locked_by(lctx)
    }
}

impl<T:LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
    pub open spec fn inv(&self) -> bool{
        &&&
        self.view().inv()
        &&&
        self.is_init()
    }
}

impl<T, ROT, GhostT,> RwLock<T, ROT, GhostT, NO_KILL_STATE>{
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
impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
    #[verifier::external_body]
    pub fn take(&mut self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>) -> (ret:T)
        requires
            old(self).wlocked_by(lctx),
            old(self).is_init() == true,

            lp@.state() is WriteLock,
            lp@.thread_id() == lctx.thread_id(),
            lp@.lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            take_ensures(*old(self), *final(self)),
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
            put_ensures(*old(self), *final(self), v),
    {
        unsafe { core::ptr::write(&mut self.value as *mut T, v) }
    }
    #[verifier::external_body]
    pub fn borrow<'a,>(&self, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.is_init() == true,

            lp@.state() is WriteLock ==> self.write_lock_perm_match(lp@),
            lp@.state() is ReadLock ==> self.read_lock_perm_match(lp@), 
    {
        unsafe{
            &*(&self.value as *const T)
        }
    }

    #[verifier::external_body]
    pub fn borrow_rodata(&self) -> (ret: &ROT)
    {
        unsafe{
            &*(&self.read_only_value as *const ROT)
        }
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, GhostT,> RwLock<T, ROT, GhostT,NO_KILL_STATE>{
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
            wlock_ensures(*old(self), *final(self), lock_id@, final(lctx).thread_id(), ret@),
            lock_ensures(old(lctx), final(lctx), final(self).view(), lock_id@),
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
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(old(lctx), final(lctx), final(self).view(), lp@.lock_id()),
    {
        self.lock.wunlock();
    }

}

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, GhostT,> RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
    #[verifier::external_body]
    pub fn try_wlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret:(bool, Option<Tracked<LockPerm>>))
        requires
            old(self)@.container_depth() == lock_id@.container,
            old(self)@.process_depth() == lock_id@.process,
            old(self)@.lock_major_sat(lock_id@.major),

            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id@),
        ensures
            ret.0 == false ==> 
            {
                &&&
                old(self).being_killed() == true
                &&&
                *old(self) == *final(self)
                &&&
                ret.1 is None
            },
            ret.0 == true ==>{
                &&&                
                old(self).being_killed() == false
                &&&
                ret.1 is Some
                &&&
                wlock_ensures(*old(self), *final(self), lock_id@, final(lctx).thread_id(), ret.1.unwrap()@)
                &&&
                lock_ensures(old(lctx), final(lctx), final(self).view(), lock_id@)
            } 
    {
        if self.lock.try_wlock().is_err(){
            (false, None)
        }else{
            (true, Some(Tracked::assume_new()))
        }

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
            old(self).being_killed() == final(self).being_killed(),
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(old(lctx), final(lctx), final(self).view(), lp@.lock_id()),
    {
        self.lock.wunlock();
    }

}

pub open spec fn wlock_requires<T: LockUserVisibilityTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, lctx: &LocalContext) -> bool{
    &&&
    old.locked_by(lctx) == false
    &&&
    lctx.kernel_view_locking_state() is Acquire
    &&&
    T::is_user_visible() ==> lctx.user_view_locking_state() is Acquire
}

pub open spec fn wlock_ensures<T:LockInvTrait + LockMajorTrait + LockUserVisibilityTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, lock_id: LockId, thread_id: LockThreadId, lock_perm:LockPerm) -> bool{
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

pub open spec fn wunlock_ensures<T:LockInvTrait + LockUserVisibilityTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>) -> bool{
    &&&
    new.locking_thread() == RwLockState::None
    &&&
    new.inv()
    &&&
    new@ == old@
}

pub open spec fn take_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == false
    &&&
    new@ == old@
}

pub open spec fn put_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, v:T) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == true
    &&&
    new@ == v
}

}
