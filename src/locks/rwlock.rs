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
    pub fn wlock_unless_killed(&mut self) -> Result<(),KillerInfo> {
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
                debug_assert!(self.writing, "wunlock called on object that is not write-locked");
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
    pub fn rlock_unless_killed(&mut self) -> Result<(),KillerInfo> {
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
                debug_assert!(self.num_of_reader > 0, "runlock called on object that is not read-locked");
                self.num_of_reader = self.num_of_reader - 1;
                self.lock.store(false, Ordering::Release);
                break;
            }
        }

    }
}

pub enum RwLockState{
    Write{thread_id: LockThreadId, lock_id: LockToken},
    Read{reader_map: Map<LockThreadId, LockToken>},
    None,
}

/// `RwLock<T, ROT, GhostT, HAS_KILL_STATE>`
///
/// The refinement projection alone decides which payload and ghost fields are
/// user-visible. Ghost replacement is proof-only and independent of payload
/// locking; callers close the affected invariants at the kernel boundary.
#[repr(C)]
pub struct RwLock<T, ROT, GhostT, const HAS_KILL_STATE: bool>{
    lock: RwLockInner,
    value: T,
    read_only_value: ROT,
    ghost_value: Ghost<GhostT>,

    is_init: Ghost<bool>,
    locking_thread: Ghost<RwLockState>,
}

impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
    pub closed spec fn locking_thread(&self) -> RwLockState
    {
        self.locking_thread.view()
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
    pub open spec fn wlocked_by_thread(&self, thread_id: LockThreadId) -> bool {
        &&&
        self.locking_thread() is Write
        &&&
        self.locking_thread()->Write_thread_id == thread_id
    }
    pub open spec fn rlocked_by_thread(&self, thread_id: LockThreadId) -> bool {
        &&&
        self.locking_thread() is Read
        &&&
        self.locking_thread()->Read_reader_map.dom().contains(thread_id)
    }
    pub open spec fn locked_by_thread(&self, thread_id: LockThreadId) -> bool {
        |||
        self.rlocked_by_thread(thread_id)
        |||
        self.wlocked_by_thread(thread_id)
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
        self.is_init.view()
    }

    pub closed spec fn view(&self) -> T
    {
        self.value
    }

    pub closed spec fn view_rodata(&self) -> ROT
    {
        self.read_only_value
    }

    pub closed spec fn view_ghost(&self) -> GhostT
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

impl<T, ROT, GhostT>
    RwLock<T, ROT, GhostT, NO_KILL_STATE>{
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

            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            take_ensures(*old(self), *final(self)),
            final(self).wlocked_by(lctx),
            ret == old(self).view(),
    {
        unsafe { core::ptr::read(&self.value as *const T) }
    }

    #[verifier::external_body]
    pub fn put(&mut self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>, v: T)
        requires
            old(self).wlocked_by(lctx),
            old(self).is_init() == false,

            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            put_ensures(*old(self), *final(self), v),
            final(self).wlocked_by(lctx),
    {
        unsafe { core::ptr::write(&mut self.value as *mut T, v) }
    }
    #[verifier::external_body]
    pub fn borrow<'a,>(&self, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.is_init() == true,

            lp.view().state() is WriteLock ==> self.write_lock_perm_match(lp.view()),
            lp.view().state() is ReadLock ==> self.read_lock_perm_match(lp.view()),
        ensures
            ret == self.view(),
    {
        unsafe{
            &*(&self.value as *const T)
        }
    }

    /// Mutably borrow the inner value while holding a write lock.
    ///
    /// The returned `&mut T` lives for as long as the borrow against `&mut self`
    /// (and against the lock perm). On drop, the inner value reflects whatever
    /// the borrow was last set to — same `&mut`-linkage Verus uses elsewhere.
    #[verifier::external_body]
    pub fn borrow_mut<'a>(&'a mut self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut T)
        requires
            old(self).wlocked_by(lctx),
            old(self).is_init(),

            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            final(self).is_init(),
            final(self).wlocked_by(lctx),
            // Invariants of the lock are preserved by the structure of the rwlock.
            final(self).view_rodata() == old(self).view_rodata(),
            final(self).view_ghost() == old(self).view_ghost(),
            final(self).locking_thread() == old(self).locking_thread(),
            final(self).being_killed() == old(self).being_killed(),

            // The `&mut T` ⇄ inner value linkage.
            *ret == old(self).view(),
            final(self).view() == *final(ret),
    {
        unsafe{
            &mut *(&mut self.value as *mut T)
        }
    }

    #[verifier::external_body]
    pub fn borrow_rodata(&self) -> (ret: &ROT)
        ensures
            ret == self.view_rodata(),
    {
        unsafe{
            &*(&self.read_only_value as *const ROT)
        }
    }

    /// Replace the proof-only ghost slot without borrowing or locking payload.
    pub proof fn update_ghost(tracked &mut self, new_ghost: GhostT)
        ensures
            update_ghost_ensures(*old(self), *final(self), new_ghost),
    {
        self.ghost_value = Ghost(new_ghost);
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait,
    ROT, GhostT>
    RwLock<T, ROT, GhostT, NO_KILL_STATE>{
    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret:Tracked<LockPerm>)
        requires
            old(self).view().container_depth() == lock_id.view().container,
            old(self).view().process_depth() == lock_id.view().process,
            old(self).view().lock_major_sat(lock_id.view().major),
            old(self).view().lock_minor() == lock_id.view().minor,

            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id.view()),
        ensures
            wlock_ensures(*old(self), *final(self), lock_id.view(), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), final(self).view(),
                lock_id.view(), obj_id.view()),
    {
        self.lock.wlock();
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),

            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,

            old(lctx).lock_id_set().contains((LockId {
                container: old(self).view().container_depth(),
                process: old(self).view().process_depth(),
                major: old(self).view().current_lock_major(),
                minor: old(self).view().lock_minor(),
            }, obj_id.view())),
        ensures
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).view(),
                lp.view().lock_id(),
                obj_id.view(),
                LockId {
                    container: old(self).view().container_depth(),
                    process: old(self).view().process_depth(),
                    major: old(self).view().current_lock_major(),
                    minor: old(self).view().lock_minor(),
                },
            ),
    {
        self.lock.wunlock();
    }

}

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait,
    ROT, GhostT>
    RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
    #[verifier::external_body]
    pub fn wlock_unless_killed(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret:(bool, Option<Tracked<LockPerm>>))
        requires
            old(self).view().container_depth() == lock_id.view().container,
            old(self).view().process_depth() == lock_id.view().process,
            old(self).view().lock_major_sat(lock_id.view().major),

            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id.view()),
        ensures
            ret.0 == false ==> 
            {
                &&&
                old(self).being_killed() == true
                &&&
                *old(self) == *final(self)
                &&&
                ret.1 is None
                &&&
                *final(lctx) == *old(lctx)
            },
            ret.0 == true ==>{
                &&&                
                old(self).being_killed() == false
                &&&
                ret.1 is Some
                &&&
                wlock_ensures(*old(self), *final(self), lock_id.view(), final(lctx), ret.1.unwrap().view())
                &&&
                lock_ensures(old(lctx), final(lctx), final(self).view(),
                    lock_id.view(), obj_id.view())
            } 
    {
        if self.lock.wlock_unless_killed().is_err(){
            (false, None)
        }else{
            (true, Some(Tracked::assume_new()))
        }

    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),

            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,

            old(lctx).lock_id_set().contains((
                lock_id.view(), obj_id.view())),
        ensures
            old(self).being_killed() == final(self).being_killed(),
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).view(),
                lp.view().lock_id(),
                obj_id.view(),
                lock_id.view(),
            ),
    {
        self.lock.wunlock();
    }

    /// Atomically write-lock the object and mark it as being-killed.
    ///
    /// Fails (with the existing killer info) if another thread already
    /// marked the object. Succeeds only on a live, currently-unlocked
    /// object.
    ///
    /// Marking is a kernel-view Release: every other thread's next `try_*`
    /// will fail with `Err`, which is externally observable. Therefore the
    /// section's `kernel_view_locking_state` flips to `Release`.
    ///
    /// On success, the killer holds a write lock and `being_killed == true`.
    /// Cleanup must be doable with the locks already held — no further locks
    /// can be acquired in this section.
    ///
    /// Note the asymmetry with `wlock_unless_killed`: a successful mark flips the
    /// kernel-view phase to `Release`, so this does NOT compose with
    /// `lock_ensures` (which would assert the new phase is `Acquire`).
    #[verifier::external_body]
    pub fn try_wlock_and_mark_kill(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>, killer_info: KillerInfo) -> (ret:(bool, Option<Tracked<LockPerm>>))
        requires
            old(self).view().container_depth() == lock_id.view().container,
            old(self).view().process_depth() == lock_id.view().process,
            old(self).view().lock_major_sat(lock_id.view().major),

            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id.view()),

        ensures
            ret.0 == false ==>
            {
                &&&
                old(self).being_killed() == true
                &&&
                *old(self) == *final(self)
                &&&
                ret.1 is None
                &&&
                *final(lctx) == *old(lctx)
            },
            ret.0 == true ==>{
                &&&
                old(self).being_killed() == false
                &&&
                final(self).being_killed() == true
                &&&
                final(self).killer_info_inner() == Some(killer_info)
                &&&
                ret.1 is Some

                // Lock acquired with the given lock_id.
                &&&
                final(self).locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.1.unwrap().view().lock_id() }
                &&&
                final(self).inv()
                &&&
                final(self).view() == old(self).view()
                &&&
                final(self).view_rodata() == old(self).view_rodata()
                &&&
                final(self).view_ghost() == old(self).view_ghost()

                // LockPerm minted.
                &&&
                ret.1.unwrap().view().state() is WriteLock
                &&&
                ret.1.unwrap().view().lock_id() == final(self).locking_thread()->Write_lock_id
                &&&
                ret.1.unwrap().view().ordering_lock_id() == lock_id.view()
                &&&
                ret.1.unwrap().view().thread_id() == final(lctx).thread_id()

                // LocalContext: lock acquired, kernel-view Release (the mark).
                &&&
                final(lctx).thread_id() == old(lctx).thread_id()
                &&&
                final(lctx).lock_id_set()
                    == old(lctx).lock_id_set()
                        .insert((lock_id.view(), obj_id.view()))
                &&&
                final(lctx).kernel_view_locking_state() is Release
            }
    {
        if self.lock.try_wlock_and_mark_kill(killer_info).is_err(){
            (false, None)
        }else{
            (true, Some(Tracked::assume_new()))
        }
    }

}

pub open spec fn wlock_requires<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, lctx: &LocalContext) -> bool{
    &&&
    // LocalContext records write ownership only.  Reader contention is handled
    // by the physical lock; there is no verified rlock acquisition path.
    old.wlocked_by(lctx) == false
    &&&
    lctx.kernel_view_locking_state() is Acquire
}

pub open spec fn wlock_ensures<T:LockInvTrait + LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, lock_id: LockId, lctx: &LocalContext, lock_perm:LockPerm) -> bool{
    &&&
    new.wlocked_by(lctx)
    &&&
    new.locking_thread() == RwLockState::Write { thread_id: lctx.thread_id(), lock_id: lock_perm.lock_id() }
    &&&
    new.inv()
    &&&
    new.view() == old.view()
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_ghost() == old.view_ghost()
    &&&
    new.being_killed() == old.being_killed()
    &&&
    old.locked() == false

    &&&
    lock_perm.state() is WriteLock
    &&&
    new.locking_thread()->Write_lock_id == lock_perm.lock_id()
    &&&
    lock_perm.ordering_lock_id() == lock_id
    &&&
    lock_perm.thread_id() == lctx.thread_id()
}

pub open spec fn wunlock_ensures<T:LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>) -> bool{
    &&&
    new.locking_thread() == RwLockState::None
    &&&
    new.inv()
    &&&
    new.view() == old.view()
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_ghost() == old.view_ghost()
    &&&
    new.being_killed() == old.being_killed()
}

pub open spec fn take_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == false
    &&&
    new.view() == old.view()
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_ghost() == old.view_ghost()
    &&&
    new.killer_info_inner() == old.killer_info_inner()
}

pub open spec fn put_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, v:T) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == true
    &&&
    new.view() == v
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_ghost() == old.view_ghost()
    &&&
    new.killer_info_inner() == old.killer_info_inner()
    &&&
    new.being_killed() == old.being_killed()
}

pub open spec fn update_ghost_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new_ghost: GhostT) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == old.is_init()
    &&&
    new.view() == old.view()
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_ghost() == new_ghost
    &&&
    new.killer_info_inner() == old.killer_info_inner()
}

impl<T:LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const HAS_KILL_STATE: bool> LockOwnerIdTrait for RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
    open spec fn container_depth(&self) -> LockOwnerId{
        if self.view_rodata().container_depth() != LockOwnerId::NotApp{
            self.view_rodata().container_depth()
        }else{
            self.view().container_depth()
        }
    }
    open spec fn process_depth(&self) -> LockOwnerId{
        if self.view_rodata().process_depth() != LockOwnerId::NotApp{
            self.view_rodata().process_depth()
        }else{
            self.view().process_depth()
        }
    }
}  

impl<T:LockIdTrait, const HAS_KILL_STATE: bool>
    LockIdTrait for RwLock<T, (), (), HAS_KILL_STATE>{
    open spec fn lock_id(&self) -> LockId {
        self.view().lock_id()
    }
}

}
