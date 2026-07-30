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

/// `RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>`
///
/// Whether each field is observable in the user view depends on
/// `T::is_user_visible()`:
///
/// - `T`        — the lock-protected payload. Always kernel-visible; also
///                user-visible iff `T::is_user_visible()`.
/// - `ROT`      — read-only data alongside the value. Always kernel-visible;
///                also user-visible iff `T::is_user_visible()`.
/// - `KGhostT`  — ghost data restricted to the kernel view. Never visible to
///                the user view, even when `T::is_user_visible()`. Updating
///                it is a kernel-view Release.
/// - `UGhostT`  — ghost data following the same visibility rule as `T`.
///                Updating it is a kernel-view Release; if
///                `T::is_user_visible()`, also requires user-view Release.
#[repr(C)]
pub struct RwLock<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>{
    lock: RwLockInner,
    value: T,
    read_only_value: ROT,
    kernel_ghost: Ghost<KGhostT>,
    user_ghost: Ghost<UGhostT>,

    is_init: Ghost<bool>,
    locking_thread: Ghost<RwLockState>,
}

impl<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
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

    pub closed spec fn view_kernel_ghost(&self) -> KGhostT
    {
        self.kernel_ghost.view()
    }

    pub closed spec fn view_user_ghost(&self) -> UGhostT
    {
        self.user_ghost.view()
    }

}

impl<T: LockRecursivelyLockedTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
    pub open spec fn partial_locked_by(&self, lctx:&LocalContext) -> bool{
        self.view().partial_locked_by(lctx)
    }    
    pub open spec fn total_locked_by(&self, lctx:&LocalContext) -> bool{
        self.view().total_locked_by(lctx)
    }
}

impl<T:LockInvTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
    pub open spec fn inv(&self) -> bool{
        &&&
        self.view().inv()
        &&&
        self.is_init()
    }
}

impl<T, ROT, KGhostT, UGhostT,> RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>{
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
impl<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
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
            old(self).is_init() == false,

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

            lp@.state() is WriteLock,
            lp@.thread_id() == lctx.thread_id(),
            lp@.lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            final(self).is_init(),
            // Invariants of the lock are preserved by the structure of the rwlock.
            final(self).view_rodata() == old(self).view_rodata(),
            final(self).view_kernel_ghost() == old(self).view_kernel_ghost(),
            final(self).view_user_ghost() == old(self).view_user_ghost(),
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

    /// Trusted proof primitive: replace the kernel-view-only ghost field.
    ///
    /// This is unconditionally a kernel-view Release because the new ghost
    /// value can be observed by any thread that subsequently locks the
    /// object. It does NOT need user-view Release because, by construction,
    /// the kernel ghost is not part of the user view.
    ///
    /// No write lock is required — that is the whole point of having a
    /// ghost slot that can be updated lock-free. Valid in both Acquire and
    /// Release phases of the kernel-view; the operation itself is a Release
    /// transition.
    ///
    /// Forbidden on tombstoned objects: once `being_killed`, the only legal
    /// op is retype.
    #[verifier::external_body]
    pub proof fn update_kernel_ghost(tracked &mut self, tracked lctx: &mut LocalContext, new_kernel_ghost: KGhostT)
        requires
            !old(self).being_killed(),
        ensures
            update_kernel_ghost_ensures(*old(self), *final(self), new_kernel_ghost),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_maps_equal(old(lctx)),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
    {
        unimplemented!()
    }
}

impl<T:LockUserVisibilityTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
    /// Trusted proof primitive: replace the user-view-visible ghost field.
    ///
    /// This is a kernel-view Release in the same sense as `update_kernel_ghost`.
    /// In addition, if `T::is_user_visible()`, the change is observable in the
    /// user view, so the syscall must have already manually linearized
    /// (user_view_locking_state is Release).
    ///
    /// Forbidden on tombstoned objects: once `being_killed`, the only legal
    /// op is retype.
    #[verifier::external_body]
    pub proof fn update_user_ghost(tracked &mut self, tracked lctx: &mut LocalContext, new_user_ghost: UGhostT)
        requires
            !old(self).being_killed(),
            T::is_user_visible() ==> old(lctx).user_view_locking_state() is Release,
        ensures
            update_user_ghost_ensures(*old(self), *final(self), new_user_ghost),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_maps_equal(old(lctx)),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),
    {
        unimplemented!()
    }
}

impl<T:LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT,> RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>{
    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret:Tracked<LockPerm>)
        requires
            old(self)@.container_depth() == lock_id@.container,
            old(self)@.process_depth() == lock_id@.process,
            old(self)@.lock_major_sat(lock_id@.major),
            old(self)@.lock_minor() == lock_id@.minor,

            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id@),
            old(lctx).obj_id_fresh(obj_id@),
        ensures
            wlock_ensures(*old(self), *final(self), lock_id@, final(lctx).thread_id(), ret@),
            lock_ensures(old(lctx), final(lctx), final(self).view(), lock_id@, obj_id@),
    {
        self.lock.wlock();
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),

            unlock_requires::<T>(old(lctx)),

            lp@.state() is WriteLock,
            lp@.thread_id() == old(lctx).thread_id(),
            lp@.lock_id() == old(self).locking_thread()->Write_lock_id,

            old(lctx).lock_map_contains(obj_id@),
        ensures
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).view(),
                lp@.lock_id(),
                obj_id@,
                old(lctx).lock_id_for_obj(obj_id@),
            ),
    {
        self.lock.wunlock();
    }

}

impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT,> RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
    #[verifier::external_body]
    pub fn wlock_unless_killed(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret:(bool, Option<Tracked<LockPerm>>))
        requires
            old(self)@.container_depth() == lock_id@.container,
            old(self)@.process_depth() == lock_id@.process,
            old(self)@.lock_major_sat(lock_id@.major),

            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id@),
            old(lctx).obj_id_fresh(obj_id@),
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
                final(lctx).lock_maps_equal(old(lctx))
            },
            ret.0 == true ==>{
                &&&                
                old(self).being_killed() == false
                &&&
                ret.1 is Some
                &&&
                wlock_ensures(*old(self), *final(self), lock_id@, final(lctx).thread_id(), ret.1.unwrap()@)
                &&&
                lock_ensures(old(lctx), final(lctx), final(self).view(), lock_id@, obj_id@)
            } 
    {
        if self.lock.wlock_unless_killed().is_err(){
            (false, None)
        }else{
            (true, Some(Tracked::assume_new()))
        }

    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),

            unlock_requires::<T>(old(lctx)),

            lp@.state() is WriteLock,
            lp@.thread_id() == old(lctx).thread_id(),
            lp@.lock_id() == old(self).locking_thread()->Write_lock_id,

            old(lctx).lock_map_contains(obj_id@),
        ensures
            old(self).being_killed() == final(self).being_killed(),
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).view(),
                lp@.lock_id(),
                obj_id@,
                old(lctx).lock_id_for_obj(obj_id@),
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
    /// section's `kernel_view_locking_state` flips to `Release`. If the
    /// object is user-visible, the precondition `user_view_locking_state is
    /// Release` enforces that the syscall has already linearized.
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
            old(self)@.container_depth() == lock_id@.container,
            old(self)@.process_depth() == lock_id@.process,
            old(self)@.lock_major_sat(lock_id@.major),

            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id@),
            old(lctx).obj_id_fresh(obj_id@),

            // Mark is a Release for the user-view too if T is user-visible.
            T::is_user_visible() ==> old(lctx).user_view_locking_state() is Release,
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
                final(self).locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.1.unwrap()@.lock_id() }
                &&&
                final(self).inv()
                &&&
                final(self)@ == old(self)@
                &&&
                final(self).view_rodata() == old(self).view_rodata()
                &&&
                final(self).view_kernel_ghost() == old(self).view_kernel_ghost()
                &&&
                final(self).view_user_ghost() == old(self).view_user_ghost()

                // LockPerm minted.
                &&&
                ret.1.unwrap()@.state() is WriteLock
                &&&
                ret.1.unwrap()@.lock_id() == final(self).locking_thread()->Write_lock_id
                &&&
                ret.1.unwrap()@.thread_id() == final(lctx).thread_id()

                // LocalContext: lock acquired, kernel-view Release (the mark).
                &&&
                final(lctx).thread_id() == old(lctx).thread_id()
                &&&
                final(lctx).lock_maps_inserted(old(lctx), obj_id@, lock_id@)
                &&&
                final(lctx).kernel_view_locking_state() is Release
                &&&
                final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state()
            }
    {
        if self.lock.try_wlock_and_mark_kill(killer_info).is_err(){
            (false, None)
        }else{
            (true, Some(Tracked::assume_new()))
        }
    }

}

pub open spec fn wlock_requires<T: LockUserVisibilityTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, lctx: &LocalContext) -> bool{
    &&&
    old.locked_by(lctx) == false
    &&&
    lctx.kernel_view_locking_state() is Acquire
    &&&
    T::is_user_visible() ==> lctx.user_view_locking_state() is Acquire
}

pub open spec fn wlock_ensures<T:LockInvTrait + LockMajorTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, lock_id: LockId, thread_id: LockThreadId, lock_perm:LockPerm) -> bool{
    &&&
    new.locking_thread() == RwLockState::Write { thread_id: thread_id, lock_id: lock_perm.lock_id() }
    &&&
    new.inv()
    &&&
    new@ == old@
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_kernel_ghost() == old.view_kernel_ghost()
    &&&
    new.view_user_ghost() == old.view_user_ghost()
    &&&
    new.being_killed() == old.being_killed()
    &&&
    old.locked() == false

    &&&
    lock_perm.state() is WriteLock
    &&&
    new.locking_thread()->Write_lock_id == lock_perm.lock_id()
    &&&
    lock_perm.thread_id() == thread_id
}

pub open spec fn wunlock_ensures<T:LockInvTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>) -> bool{
    &&&
    new.locking_thread() == RwLockState::None
    &&&
    new.inv()
    &&&
    new@ == old@
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_kernel_ghost() == old.view_kernel_ghost()
    &&&
    new.view_user_ghost() == old.view_user_ghost()
    &&&
    new.being_killed() == old.being_killed()
}

pub open spec fn take_ensures<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == false
    &&&
    new@ == old@
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_kernel_ghost() == old.view_kernel_ghost()
    &&&
    new.view_user_ghost() == old.view_user_ghost()
    &&&
    new.killer_info_inner() == old.killer_info_inner()
}

pub open spec fn put_ensures<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, v:T) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == true
    &&&
    new@ == v
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_kernel_ghost() == old.view_kernel_ghost()
    &&&
    new.view_user_ghost() == old.view_user_ghost()
    &&&
    new.killer_info_inner() == old.killer_info_inner()
}

pub open spec fn update_kernel_ghost_ensures<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, new_kernel_ghost: KGhostT) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == old.is_init()
    &&&
    new@ == old@
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_user_ghost() == old.view_user_ghost()
    &&&
    new.view_kernel_ghost() == new_kernel_ghost
    &&&
    new.killer_info_inner() == old.killer_info_inner()
}

pub open spec fn update_user_ghost_ensures<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(old:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, new:RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>, new_user_ghost: UGhostT) -> bool{
    &&&
    new.locking_thread() == old.locking_thread()
    &&&
    new.is_init() == old.is_init()
    &&&
    new@ == old@
    &&&
    new.view_rodata() == old.view_rodata()
    &&&
    new.view_kernel_ghost() == old.view_kernel_ghost()
    &&&
    new.view_user_ghost() == new_user_ghost
    &&&
    new.killer_info_inner() == old.killer_info_inner()
}

impl<T:LockOwnerIdTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT, const HAS_KILL_STATE: bool> LockOwnerIdTrait for RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>{
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

impl<T:LockIdTrait, const HAS_KILL_STATE: bool> LockIdTrait for RwLock<T, (), (), (), HAS_KILL_STATE>{
    open spec fn lock_id(&self) -> LockId {
        self.view().lock_id()
    }
}

}
