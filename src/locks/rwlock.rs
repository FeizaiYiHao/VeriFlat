use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use crate::locks::*;

// Platform implementation: clear and set the calling cpu's interrupt flag.
unsafe extern "C" {
    fn veriflat_disable_interrupts();
    fn veriflat_enable_interrupts();
}

verus! {
#[derive(Clone,Copy)]
pub struct KillerInfo {
    pub container: RwLockContainerPtr,
    pub container_depth: usize,

    pub process: RwLockProcessPtr,
    pub process_depth: usize,

    pub thread: RwLockThreadPtr,

    pub cpu_id: CpuId,
}

/// Control word of a lock. Non-dynamic locks use only `Clear` and `Killed`; a dynamic lock records the concrete owner
/// of its current write acquisition as `DynamicProcess`. Its layout is fixed by the assertions at the end of this file.
#[derive(Clone,Copy)]
pub enum LockControl {
    Clear,
    DynamicProcess(LockOwnerId),
    Killed(KillerInfo),
}

/// Outcome of a dynamic write acquisition: the lock, the existing kill record, or the shallower concrete owner of a
/// live holder that the requested owner must not wait for.
pub enum DynamicWLockResult {
    Acquired(Tracked<LockPerm>),
    Killed(KillerInfo),
    DepthConflict { observed_owner: LockOwnerId },
}

pub struct RwLockInner {
    lock: AtomicBool, // false means no one is read/writing the lock content.
    writing: bool,
    num_of_reader: usize, // right now we don't need to worry about overflow because we don't support kernel interrupt.

    control: LockControl,
}

impl RwLockInner {
    #[verifier::external_body]
    pub fn wlock(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                if self.num_of_reader == 0 && self.writing == false {
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
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                if let LockControl::Killed(ret) = self.control {
                    self.lock.store(false, Ordering::Release);
                    return Err(ret);
                }
                if self.num_of_reader == 0 && self.writing == false {
                    self.writing = true;
                    self.lock.store(false, Ordering::Release);
                    return Ok(());
                }
                self.lock.store(false, Ordering::Release);
            }
        }
    }

    /// `wlock_unless_killed` that clears the calling cpu's interrupt flag under the guard when it grants the lock.
    #[verifier::external_body]
    pub fn wlock_unless_killed_cli(&mut self) -> Result<(),KillerInfo> {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                if let LockControl::Killed(ret) = self.control {
                    self.lock.store(false, Ordering::Release);
                    return Err(ret);
                }
                if self.num_of_reader == 0 && self.writing == false {
                    self.writing = true;
                    unsafe { veriflat_disable_interrupts(); }
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
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                if let LockControl::Killed(ret) = self.control {
                    self.lock.store(false, Ordering::Release);
                    return Err(ret);
                }
                if self.num_of_reader == 0 && self.writing == false {
                    self.writing = true;
                    self.control = LockControl::Killed(killer_info);
                    self.lock.store(false, Ordering::Release);
                    return Ok(());
                }
                self.lock.store(false, Ordering::Release);
            }
        }
    }

    /// Record `killer_info` on an object the caller already write-holds.
    #[verifier::external_body]
    pub fn mark_kill(&mut self, killer_info: KillerInfo) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                debug_assert!(self.writing, "mark_kill called on object that is not write-locked");
                self.control = LockControl::Killed(killer_info);
                self.lock.store(false, Ordering::Release);
                break;
            }
        }
    }

    /// Clear the mark of a cpu lock the caller already write-holds and marked.
    #[verifier::external_body]
    pub fn unkill(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                debug_assert!(self.writing && matches!(self.control, LockControl::Killed(_)), "unkill called on object that is not write-locked and marked");
                self.control = LockControl::Clear;
                self.lock.store(false, Ordering::Release);
                break;
            }
        }
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                debug_assert!(self.writing, "wunlock called on object that is not write-locked");
                self.writing = false;
                self.lock.store(false, Ordering::Release);
                break;
            }
        }
    }

    /// `wunlock` that sets the calling cpu's interrupt flag once the lock is released.
    #[verifier::external_body]
    pub fn wunlock_sti(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                debug_assert!(self.writing, "wunlock_sti called on object that is not write-locked");
                self.writing = false;
                self.lock.store(false, Ordering::Release);
                unsafe { veriflat_enable_interrupts(); }
                break;
            }
        }
    }

    /// Dynamic write acquisition for the concrete owner `requested`. Under the guard, every iteration first reports a
    /// kill record, then a live writer whose recorded owner is below `requested`; a free lock is taken and records
    /// `requested`; any other holder is waited for.
    #[verifier::external_body]
    pub fn dynamic_wlock(&mut self, requested: LockOwnerId) -> Result<(), LockControl> {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                match self.control {
                    LockControl::Killed(killer_info) => {
                        self.lock.store(false, Ordering::Release);
                        return Err(LockControl::Killed(killer_info));
                    }
                    LockControl::DynamicProcess(holder) => {
                        if self.writing && lock_owner_lt(holder, requested) {
                            self.lock.store(false, Ordering::Release);
                            return Err(LockControl::DynamicProcess(holder));
                        }
                    }
                    LockControl::Clear => {}
                }
                if self.num_of_reader == 0 && self.writing == false {
                    self.writing = true;
                    self.control = LockControl::DynamicProcess(requested);
                    self.lock.store(false, Ordering::Release);
                    return Ok(());
                }
                self.lock.store(false, Ordering::Release);
            }
        }
    }

    /// Release a live dynamic write acquisition and clear its recorded owner in the same guarded update.
    #[verifier::external_body]
    pub fn dynamic_wunlock(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                debug_assert!(self.writing, "dynamic_wunlock called on object that is not write-locked");
                self.writing = false;
                self.control = LockControl::Clear;
                self.lock.store(false, Ordering::Release);
                break;
            }
        }
    }

    #[verifier::external_body]
    pub fn rlock(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                if self.writing == false {
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
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                if let LockControl::Killed(ret) = self.control {
                    self.lock.store(false, Ordering::Release);
                    return Err(ret);
                }
                if self.writing == false {
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
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                debug_assert!(self.num_of_reader > 0, "runlock called on object that is not read-locked");
                self.num_of_reader = self.num_of_reader - 1;
                self.lock.store(false, Ordering::Release);
                break;
            }
        }
    }

    /// Turn the caller's write lock into its sole read lock without letting another writer in.
    #[verifier::external_body]
    pub fn downgrade(&mut self) {
        loop {
            if self.lock.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                debug_assert!(self.writing, "downgrade called on object that is not write-locked");
                self.writing = false;
                self.num_of_reader = 1;
                self.lock.store(false, Ordering::Release);
                break;
            }
        }
    }
}

/// Observable mode of a lock, independent of ownership and reader count.
pub ghost enum LockStateU { Unlocked, ReadLocked, WriteLocked }

pub enum RwLockState {
    Write { thread_id: LockThreadId, lock_id: LockToken },
    Read { reader_map: Map<LockThreadId, LockToken> },
    None,
}

/// `RwLock<T, ROT, GhostT, HAS_KILL_STATE>`
///
/// The refinement projection alone decides which payload and ghost fields are
/// user-visible. Ghost replacement is proof-only and independent of payload
/// locking; callers close the affected invariants at the kernel boundary.
#[repr(C)]
pub struct RwLock<T, ROT, GhostT, const HAS_KILL_STATE: bool> {
    lock: RwLockInner,
    value: T,
    read_only_value: ROT,
    ghost_value: Ghost<GhostT>,

    is_init: Ghost<bool>,
    locking_thread: Ghost<RwLockState>,
}

impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, GhostT, HAS_KILL_STATE> {
    pub fn new_unlocked(value: T, read_only_value: ROT, Ghost(ghost_value): Ghost<GhostT>) -> (ret: Self)
        where
            T: LockInvTrait,
        requires
            value.inv(),
        ensures
            ret.inv(),
            ret.view() == value,
            ret.view_rodata() == read_only_value,
            ret.view_ghost() == ghost_value,
            ret.locking_thread() is None,
            !ret.locked(),
            !ret.being_killed(),
    {
        Self {
            lock: RwLockInner { lock: AtomicBool::new(false), writing: false, num_of_reader: 0, control: LockControl::Clear },
            value, read_only_value, ghost_value: Ghost(ghost_value), is_init: Ghost(true), locking_thread: Ghost(RwLockState::None),
        }
    }

    /// TCB: runtime image of a freshly retyped object that its creator holds write-locked under `control` (`Clear`, or
    /// `DynamicProcess` for a dynamic lock). Only the retype primitives use it; their contracts supply the ghost state.
    #[verifier::external]
    pub fn new_wlocked_for_retype(value: T, read_only_value: ROT, control: LockControl) -> Self {
        Self {
            lock: RwLockInner { lock: AtomicBool::new(false), writing: true, num_of_reader: 0, control },
            value, read_only_value, ghost_value: Ghost::assume_new(), is_init: Ghost::assume_new(), locking_thread: Ghost::assume_new(),
        }
    }

    pub open spec fn lock_state_u(&self) -> LockStateU {
        match self.locking_thread() {
            RwLockState::None => LockStateU::Unlocked,
            RwLockState::Read { .. } => LockStateU::ReadLocked,
            RwLockState::Write { .. } => LockStateU::WriteLocked,
        }
    }

    pub closed spec fn locking_thread(&self) -> RwLockState
    {
        self.locking_thread.view()
    }
    pub open spec fn locked(&self) -> bool {
        ||| self.rlocked()
        ||| self.wlocked()
    }
    pub open spec fn rlocked(&self) -> bool {
        &&& self.locking_thread() is Read
    }
    pub open spec fn rlocked_by(&self, lctx: &LocalContext) -> bool {
        &&& self.locking_thread() is Read
        &&& self.locking_thread()->Read_reader_map.dom().contains(lctx.thread_id())
    }
    pub open spec fn read_lock_perm_match(&self, lock_perm: &LockPerm) -> bool {
        &&& self.locking_thread() is Read
        &&& self.locking_thread()->Read_reader_map.dom().contains(lock_perm.thread_id())
        &&& self.locking_thread()->Read_reader_map.spec_index(lock_perm.thread_id()) == lock_perm.lock_id()
    }
    pub open spec fn write_lock_perm_match(&self, lock_perm: &LockPerm) -> bool {
        &&& self.locking_thread() is Write
        &&& self.locking_thread()->Write_thread_id == lock_perm.thread_id()
        &&& self.locking_thread()->Write_lock_id == lock_perm.lock_id()
    }

    pub open spec fn wlocked(&self) -> bool {
        &&& self.locking_thread() is Write
    }
    pub open spec fn wlocked_by(&self, lctx: &LocalContext) -> bool {
        &&& self.locking_thread() is Write
        &&& self.locking_thread()->Write_thread_id == lctx.thread_id()
    }
    pub open spec fn wlocked_by_thread(&self, thread_id: LockThreadId) -> bool {
        &&& self.locking_thread() is Write
        &&& self.locking_thread()->Write_thread_id == thread_id
    }
    pub open spec fn rlocked_by_thread(&self, thread_id: LockThreadId) -> bool {
        &&& self.locking_thread() is Read
        &&& self.locking_thread()->Read_reader_map.dom().contains(thread_id)
    }
    pub open spec fn locked_by_thread(&self, thread_id: LockThreadId) -> bool {
        ||| self.rlocked_by_thread(thread_id)
        ||| self.wlocked_by_thread(thread_id)
    }
    pub open spec fn locked_by(&self, lctx: &LocalContext) -> bool {
        ||| self.rlocked_by(lctx)
        ||| self.wlocked_by(lctx)
    }
    pub closed spec fn control(&self) -> LockControl { self.lock.control }
    pub open spec fn killer_info_inner(&self) -> Option<KillerInfo> {
        match self.control() { LockControl::Killed(killer_info) => Some(killer_info), _ => None }
    }
    /// Concrete owner recorded by the current dynamic write acquisition.
    pub open spec fn dynamic_process_owner(&self) -> Option<LockOwnerId> {
        match self.control() { LockControl::DynamicProcess(owner) => Some(owner), _ => None }
    }
    /// User-visible owner of a live dynamic write acquisition; absent unless write-held under a recorded owner.
    pub open spec fn lock_process_owner_u(&self) -> Option<LockOwnerId> {
        if self.locking_thread() is Write { self.dynamic_process_owner() } else { None }
    }
    pub open spec fn killer_info(&self) -> Option<KillerInfo> {
        if HAS_KILL_STATE { self.killer_info_inner() } else { None }
    }
    pub open spec fn being_killed(&self) -> bool {
        if HAS_KILL_STATE { self.killer_info_inner() is Some } else { false }
    }
    pub closed spec fn is_init(&self) -> bool { self.is_init.view() }

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

impl<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, GhostT, HAS_KILL_STATE> {
    pub open spec fn inv(&self) -> bool {
        &&& self.view().inv()
        &&& self.is_init()
        &&& self.locking_thread() is Read ==> !self.locking_thread()->Read_reader_map.dom().is_empty()
    }
}

impl<T, ROT, GhostT> RwLock<T, ROT, GhostT, NO_KILL_STATE> {
    #[verifier::external_body]
    pub fn wlock_external(&mut self, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
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

    #[verifier::external_body]
    pub fn rlock_external(&mut self, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<LockPerm>)
        requires
            true == false, // this function can only be called in the TCB
    {
        self.lock.rlock();
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn runlock_external(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>)
        requires
            true == false, // this function can only be called in the TCB
    {
        self.lock.runlock();
    }

    #[verifier::external_body]
    pub fn downgrade_external(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>) -> (ret: Tracked<LockPerm>)
        requires
            true == false, // this function can only be called in the TCB
    {
        self.lock.downgrade();
        Tracked::assume_new()
    }
}
impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> RwLock<T, ROT, GhostT, HAS_KILL_STATE> {
    #[verifier::external_body]
    pub fn take(&mut self, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>) -> (ret: T)
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
        unsafe { &*(&self.value as *const T) }
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
            final(self).control() == old(self).control(),
            // The `&mut T` ⇄ inner value linkage.
            *ret == old(self).view(),
            final(self).view() == *final(ret),
    {
        unsafe { &mut *(&mut self.value as *mut T) }
    }

    #[verifier::external_body]
    pub fn borrow_rodata(&self) -> (ret: &ROT)
        ensures
            ret == self.view_rodata(),
    {
        unsafe { &*(&self.read_only_value as *const ROT) }
    }

    /// Replace the proof-only ghost slot without borrowing or locking payload.
    pub proof fn update_ghost(tracked &mut self, new_ghost: GhostT)
        ensures
            update_ghost_ensures(*old(self), *final(self), new_ghost),
    {
        self.ghost_value = Ghost(new_ghost);
    }

    pub fn set_ghost(&mut self, Ghost(new_ghost): Ghost<GhostT>, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&LockPerm>)
        requires
            old(self).wlocked_by(lctx),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
        ensures
            update_ghost_ensures(*old(self), *final(self), new_ghost),
    {
        self.ghost_value = Ghost(new_ghost);
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait, ROT, GhostT> RwLock<T, ROT, GhostT, NO_KILL_STATE> {
    #[verifier::external_body]
    pub fn rlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        where ROT: LockOwnerIdTrait,
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            old(self).view().container_depth() == lock_id.view().container,
            old(self).view().process_depth() == lock_id.view().process,
            old(self).view().lock_major_sat(lock_id.view().major),
            old(self).view().lock_minor() == lock_id.view().minor,
            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id.view()),
        ensures
            rlock_ensures(*old(self), *final(self), lock_id.view(), final(lctx), ret.view()),
            rlock_lctx_ensures(old(lctx), final(lctx), lock_id.view(), obj_id.view()),
    {
        self.lock.rlock();
        Tracked::assume_new()
    }

    #[verifier::external_body]
    pub fn runlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        where ROT: LockOwnerIdTrait,
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            old(self).rlocked_by(old(lctx)),
            old(self).inv(),
            lp.view().state() is ReadLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            old(self).read_lock_perm_match(&lp.view()),
            old(lctx).lock_entry_contains(LockId { container: old(self).view().container_depth(), process: old(self).view().process_depth(), major: old(self).view().current_lock_major(), minor: old(self).view().lock_minor() }, obj_id.view()),
        ensures
            runlock_ensures(*old(self), *final(self), old(lctx).thread_id()),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
                container: old(self).view().container_depth(), process: old(self).view().process_depth(), major: old(self).view().current_lock_major(), minor: old(self).view().lock_minor() }),
    {
        self.lock.runlock();
    }

    #[verifier::external_body]
    pub fn wlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).view().container_depth() == lock_id.view().container,
            old(self).view().process_depth() == lock_id.view().process,
            old(self).view().lock_major_sat(lock_id.view().major),
            old(self).view().lock_minor() == lock_id.view().minor,
            wlock_requires(*old(self), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id.view()),
        ensures
            wlock_ensures(*old(self), *final(self), lock_id.view(), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), lock_id.view(), obj_id.view()),
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
            old(lctx).lock_entry_contains(LockId { container: old(self).view().container_depth(), process: old(self).view().process_depth(), major: old(self).view().current_lock_major(), minor: old(self).view().lock_minor() }, obj_id.view()),
        ensures
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
                container: old(self).view().container_depth(), process: old(self).view().process_depth(), major: old(self).view().current_lock_major(), minor: old(self).view().lock_minor() }),
    {
        self.lock.wunlock();
    }

    /// Turn this thread's write lock into a read lock under the same token and ordering id; the held-lock entry keeps
    /// its id and changes only its mode.
    #[verifier::external_body]
    pub fn downgrade(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        where ROT: LockOwnerIdTrait,
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(LockId { container: old(self).view().container_depth(), process: old(self).view().process_depth(), major: old(self).view().current_lock_major(), minor: old(self).view().lock_minor() }, obj_id.view()),
        ensures
            downgrade_ensures(*old(self), *final(self), final(lctx), lp.view(), ret.view()),
            downgrade_lctx_ensures(old(lctx), final(lctx), LockId {
                container: old(self).view().container_depth(), process: old(self).view().process_depth(), major: old(self).view().current_lock_major(), minor: old(self).view().lock_minor() }, obj_id.view()),
    {
        self.lock.downgrade();
        Tracked::assume_new()
    }
}

// The ordinary kill-state entry points below take no dynamic owner, so they refuse read-only data that selects a
// `Dynamic` owner component; dynamic locks use the dynamic entry points.
impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT> RwLock<T, ROT, GhostT, HAS_KILL_STATE> {
    #[verifier::external_body]
    pub fn wlock_unless_killed(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            wlock_requires(*old(self), old(lctx)),
            !old(self).being_killed() ==> {
                &&& old(self).view().container_depth() == lock_id.view().container
                &&& old(self).view().process_depth() == lock_id.view().process
                &&& old(self).view().lock_major_sat(lock_id.view().major)
                &&& old(lctx).lock_id_acyclic(lock_id.view())
            },
        ensures
            ret is None ==> {
                &&& old(self).being_killed() == true
                &&& *old(self) == *final(self)
                &&& *final(lctx) == *old(lctx)
            },
            ret is Some ==> {
                &&& old(self).being_killed() == false
                &&& wlock_ensures(*old(self), *final(self), lock_id.view(), final(lctx), ret.unwrap().view())
                &&& lock_ensures(old(lctx), final(lctx), lock_id.view(), obj_id.view())
            }
    {
        if self.lock.wlock_unless_killed().is_err() {
            None
        } else {
            Some(Tracked::assume_new())
        }
    }

    #[verifier::external_body]
    pub fn wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>)
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(lock_id.view(), obj_id.view()),
        ensures
            old(self).being_killed() == final(self).being_killed(),
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), lock_id.view()),
    {
        self.lock.wunlock();
    }

    /// `wlock_unless_killed` that also clears the calling cpu's interrupt flag when it takes the lock.
    #[verifier::external_body]
    pub fn wlock_unless_killed_cli(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret: Option<Tracked<LockPerm>>)
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            wlock_requires(*old(self), old(lctx)),
            !old(self).being_killed() ==> {
                &&& old(self).view().container_depth() == lock_id.view().container
                &&& old(self).view().process_depth() == lock_id.view().process
                &&& old(self).view().lock_major_sat(lock_id.view().major)
                &&& old(lctx).lock_id_acyclic(lock_id.view())
            },
        ensures
            ret is None ==> {
                &&& old(self).being_killed() == true
                &&& *old(self) == *final(self)
                &&& *final(lctx) == *old(lctx)
            },
            ret is Some ==> {
                &&& old(self).being_killed() == false
                &&& wlock_ensures(*old(self), *final(self), lock_id.view(), final(lctx), ret.unwrap().view())
                &&& lock_ensures(old(lctx), final(lctx), lock_id.view(), obj_id.view())
            }
    {
        if self.lock.wlock_unless_killed_cli().is_err() {
            None
        } else {
            Some(Tracked::assume_new())
        }
    }

    /// `wunlock` that also sets the calling cpu's interrupt flag after the release.
    #[verifier::external_body]
    pub fn wunlock_sti(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>)
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(lock_id.view(), obj_id.view()),
        ensures
            old(self).being_killed() == final(self).being_killed(),
            wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), lock_id.view()),
    {
        self.lock.wunlock_sti();
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
    pub fn try_wlock_and_mark_kill(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>, killer_info: KillerInfo) -> (ret: (bool, Option<Tracked<LockPerm>>))
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            wlock_requires(*old(self), old(lctx)),
            !old(self).being_killed() ==> {
                &&& old(self).view().container_depth() == lock_id.view().container
                &&& old(self).view().process_depth() == lock_id.view().process
                &&& old(self).view().lock_major_sat(lock_id.view().major)
                &&& old(lctx).lock_id_acyclic(lock_id.view())
            },
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret.0 == false ==> {
                &&& old(self).being_killed() == true
                &&& *old(self) == *final(self)
                &&& ret.1 is None
                &&& *final(lctx) == *old(lctx)
            },
            ret.0 == true ==> {
                &&& old(self).being_killed() == false
                // Like `wlock`, the mark is taken only once the lock is free.
                &&& old(self).locked() == false
                &&& final(self).being_killed() == true
                &&& final(self).killer_info_inner() == Some(killer_info)
                &&& ret.1 is Some
                // Lock acquired with the given lock_id.
                &&& final(self).locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.1.unwrap().view().lock_id() }
                &&& final(self).inv()
                &&& final(self).view() == old(self).view()
                &&& final(self).view_rodata() == old(self).view_rodata()
                &&& final(self).view_ghost() == old(self).view_ghost()
                // LockPerm minted.
                &&& ret.1.unwrap().view().state() is WriteLock
                &&& ret.1.unwrap().view().lock_id() == final(self).locking_thread()->Write_lock_id
                &&& ret.1.unwrap().view().ordering_lock_id() == lock_id.view()
                &&& ret.1.unwrap().view().thread_id() == final(lctx).thread_id()
                // LocalContext: lock acquired under the pre-mark id, kernel-view Release (the mark). The
                // verified wrapper must `update_lock_id` the entry to the sunk id afterwards.
                &&& final(lctx).thread_id() == old(lctx).thread_id()
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock { lock_id: lock_id.view(), mode: TypedLockMode::Write })
            }
    {
        if self.lock.try_wlock_and_mark_kill(killer_info).is_err() {
            (false, None)
        } else {
            (true, Some(Tracked::assume_new()))
        }
    }

    /// Mark an object this thread already write-holds for its killer; the write lock stays. Like
    /// `try_wlock_and_mark_kill`, the mark is a kernel-view Release: every other thread's next `try_*` fails. A mark is
    /// never cleared; the marked object is destroyed while its killer still holds it.
    #[verifier::external_body]
    pub fn mark_kill(&mut self, Tracked(lctx): Tracked<&LocalContext>, killer_info: KillerInfo)
        requires
            !(old(self).view_rodata().container_source() is Dynamic),
            !(old(self).view_rodata().process_source() is Dynamic),
            old(self).wlocked_by(lctx),
            !old(self).being_killed(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).being_killed(),
            final(self).killer_info_inner() == Some(killer_info),
            final(self).locking_thread() == old(self).locking_thread(),
            final(self).is_init() == old(self).is_init(),
            final(self).view() == old(self).view(),
            final(self).view_rodata() == old(self).view_rodata(),
            final(self).view_ghost() == old(self).view_ghost(),
    {
        self.lock.mark_kill(killer_info);
    }

    /// TCB-only access to `RwLockInner::unkill`; the cpu-lock primitive `CpuLockedArray::unkill` states its contract.
    #[verifier::external_body]
    pub fn unkill_external(&mut self)
        requires
            true == false, // this function can only be called in the TCB
    {
        self.lock.unkill();
    }
}

impl<T: LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT> RwLock<T, ROT, GhostT, HAS_KILL_STATE> {
    /// Dynamic write acquisition for the concrete owner `requested` under the candidate ordering id `lock_id`.
    #[verifier::external_body]
    pub fn dynamic_wlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>, requested: LockOwnerId) -> (ret: DynamicWLockResult)
        requires
            old(self).view_rodata().process_source() is Dynamic,
            wlock_requires(*old(self), old(lctx)),
            !old(self).being_killed() ==> {
                &&& old(self).container_depth() == lock_id.view().container
                &&& lock_id.view().process == requested
                &&& old(self).view().lock_major_sat(lock_id.view().major)
                &&& old(lctx).lock_id_acyclic(lock_id.view())
            },
        ensures
            dynamic_wlock_ensures(*old(self), *final(self), old(lctx), final(lctx), lock_id.view(), obj_id.view(), requested, ret),
    {
        match self.lock.dynamic_wlock(requested) {
            Ok(()) => DynamicWLockResult::Acquired(Tracked::assume_new()),
            Err(LockControl::Killed(killer_info)) => DynamicWLockResult::Killed(killer_info),
            Err(LockControl::DynamicProcess(observed_owner)) => DynamicWLockResult::DepthConflict { observed_owner },
            Err(LockControl::Clear) => unreachable!(),
        }
    }

    /// Release this thread's live dynamic write acquisition, registered under `lock_id`.
    #[verifier::external_body]
    pub fn dynamic_wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).view_rodata().process_source() is Dynamic,
            !old(self).being_killed(),
            old(self).wlocked_by(old(lctx)),
            old(self).inv(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(lock_id.view(), obj_id.view()),
        ensures
            dynamic_wunlock_ensures(*old(self), *final(self)),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), lock_id.view()),
    {
        self.lock.dynamic_wunlock();
    }

    /// `try_wlock_and_mark_kill` for a dynamic lock, registered under the candidate `lock_id` of the killer owner `High`.
    /// It waits for any holder and never reports a depth conflict, which is lock-order-safe only for `High`.
    #[verifier::external_body]
    pub fn try_wlock_dynamic_and_mark_kill(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>,
        Ghost(requested): Ghost<LockOwnerId>, killer_info: KillerInfo) -> (ret: (bool, Option<Tracked<LockPerm>>))
        requires
            requested == LockOwnerId::High,
            old(self).view_rodata().process_source() is Dynamic,
            wlock_requires(*old(self), old(lctx)),
            !old(self).being_killed() ==> {
                &&& old(self).container_depth() == lock_id.view().container
                &&& lock_id.view().process == requested
                &&& old(self).view().lock_major_sat(lock_id.view().major)
                &&& old(lctx).lock_id_acyclic(lock_id.view())
            },
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            ret.0 == false ==> {
                &&& old(self).being_killed() == true
                &&& *old(self) == *final(self)
                &&& ret.1 is None
                &&& *final(lctx) == *old(lctx)
            },
            ret.0 == true ==> {
                &&& old(self).being_killed() == false
                &&& old(self).locked() == false
                &&& final(self).being_killed() == true
                &&& final(self).killer_info_inner() == Some(killer_info)
                &&& ret.1 is Some
                &&& final(self).locking_thread() == RwLockState::Write { thread_id: final(lctx).thread_id(), lock_id: ret.1.unwrap().view().lock_id() }
                &&& final(self).inv()
                &&& final(self).view() == old(self).view()
                &&& final(self).view_rodata() == old(self).view_rodata()
                &&& final(self).view_ghost() == old(self).view_ghost()
                &&& ret.1.unwrap().view().state() is WriteLock
                &&& ret.1.unwrap().view().ordering_lock_id() == lock_id.view()
                &&& ret.1.unwrap().view().thread_id() == final(lctx).thread_id()
                &&& final(lctx).thread_id() == old(lctx).thread_id()
                &&& final(lctx).kernel_view_locking_state() is Release
                &&& typed_lock_maps_inserted(old(lctx), final(lctx), obj_id.view(), TypedHeldLock { lock_id: lock_id.view(), mode: TypedLockMode::Write })
            }
    {
        if self.lock.try_wlock_and_mark_kill(killer_info).is_err() {
            (false, None)
        } else {
            (true, Some(Tracked::assume_new()))
        }
    }
}

pub open spec fn wlock_requires<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    &&& old.inv()
    // The acquiring thread must hold neither a read nor a write lock here; other
    // threads' contention is handled by the physical lock.
    &&& old.locked_by(lctx) == false
    &&& lctx.kernel_view_locking_state() is Acquire
}

pub open spec fn wlock_ensures<T: LockInvTrait + LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, lock_id: LockId, lctx: &LocalContext, lock_perm: LockPerm) -> bool {
    &&& new.wlocked_by(lctx)
    &&& new.locking_thread() == RwLockState::Write { thread_id: lctx.thread_id(), lock_id: lock_perm.lock_id() }
    &&& new.inv()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.being_killed() == old.being_killed()
    &&& new.killer_info() == old.killer_info()
    &&& new.control() == old.control()
    &&& old.locked() == false
    &&& lock_perm.state() is WriteLock
    &&& new.locking_thread()->Write_lock_id == lock_perm.lock_id()
    &&& lock_perm.ordering_lock_id() == lock_id
    &&& lock_perm.thread_id() == lctx.thread_id()
}

/// Readers share the object: the new reader joins the existing reader map (or starts one).
pub open spec fn rlock_ensures<T: LockInvTrait + LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, lock_id: LockId, lctx: &LocalContext, lock_perm: LockPerm) -> bool {
    &&& new.rlocked_by(lctx)
    &&& new.locking_thread() == RwLockState::Read { reader_map: (if old.locking_thread() is Read { old.locking_thread()->Read_reader_map } else { Map::empty() }).insert(lctx.thread_id(), lock_perm.lock_id()) }
    &&& new.inv()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.being_killed() == old.being_killed()
    &&& new.control() == old.control()
    &&& old.wlocked() == false
    &&& lock_perm.state() is ReadLock
    &&& new.read_lock_perm_match(&lock_perm)
    &&& lock_perm.ordering_lock_id() == lock_id
    &&& lock_perm.thread_id() == lctx.thread_id()
}

pub open spec fn runlock_ensures<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, thread_id: LockThreadId) -> bool {
    &&& new.locking_thread() == (if old.locking_thread()->Read_reader_map.remove(thread_id).dom().is_empty() { RwLockState::None } else { RwLockState::Read { reader_map: old.locking_thread()->Read_reader_map.remove(thread_id) } })
    &&& new.inv()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.being_killed() == old.being_killed()
    &&& new.control() == old.control()
}

pub open spec fn wunlock_ensures<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>) -> bool {
    &&& new.locking_thread() == RwLockState::None
    &&& new.inv()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.being_killed() == old.being_killed()
    &&& new.killer_info() == old.killer_info()
    &&& new.control() == old.control()
}

/// A dynamic write acquisition of the free, live lock records `requested`; a kill record or a shallower live dynamic
/// holder is reported without changing the lock or the local context.
pub open spec fn dynamic_wlock_ensures<T: LockInvTrait + LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(
    old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, old_lctx: &LocalContext, new_lctx: &LocalContext,
    lock_id: LockId, obj_id: KernelObjId, requested: LockOwnerId, ret: DynamicWLockResult,
) -> bool {
    match ret {
        DynamicWLockResult::Killed(killer_info) => {
            &&& old.killer_info_inner() == Some(killer_info)
            &&& new == old
            &&& *new_lctx == *old_lctx
        },
        DynamicWLockResult::DepthConflict { observed_owner } => {
            &&& old.killer_info_inner() is None
            &&& old.wlocked()
            &&& old.dynamic_process_owner() == Some(observed_owner)
            &&& observed_owner < requested
            &&& new == old
            &&& *new_lctx == *old_lctx
        },
        DynamicWLockResult::Acquired(lock_perm) => {
            &&& old.killer_info_inner() is None
            &&& old.locked() == false
            &&& new.locking_thread() == RwLockState::Write { thread_id: new_lctx.thread_id(), lock_id: lock_perm.view().lock_id() }
            &&& new.inv()
            &&& new.view() == old.view()
            &&& new.view_rodata() == old.view_rodata()
            &&& new.view_ghost() == old.view_ghost()
            &&& new.control() == LockControl::DynamicProcess(requested)
            &&& lock_perm.view().state() is WriteLock
            &&& lock_perm.view().ordering_lock_id() == lock_id
            &&& lock_perm.view().thread_id() == new_lctx.thread_id()
            &&& lock_ensures(old_lctx, new_lctx, lock_id, obj_id)
        },
    }
}

/// Releasing a live dynamic write acquisition clears the recorded owner; payload, read-only data, and ghost stay.
pub open spec fn dynamic_wunlock_ensures<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>) -> bool {
    &&& new.locking_thread() == RwLockState::None
    &&& new.inv()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.control() == LockControl::Clear
}

/// The writer becomes the only reader under its write token; payload, ghost slot, and kill state stay.
pub open spec fn downgrade_ensures<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, lctx: &LocalContext, old_perm: LockPerm, new_perm: LockPerm) -> bool {
    &&& new.locking_thread() == RwLockState::Read { reader_map: Map::empty().insert(lctx.thread_id(), old_perm.lock_id()) }
    &&& new.inv()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.being_killed() == old.being_killed()
    &&& new.killer_info() == old.killer_info()
    &&& new.control() == old.control()
    &&& new_perm.state() is ReadLock
    &&& new_perm.lock_id() == old_perm.lock_id()
    &&& new_perm.ordering_lock_id() == old_perm.ordering_lock_id()
    &&& new_perm.thread_id() == old_perm.thread_id()
    &&& new.read_lock_perm_match(&new_perm)
}

pub open spec fn take_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>) -> bool {
    &&& new.locking_thread() == old.locking_thread()
    &&& new.is_init() == false
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.control() == old.control()
}

pub open spec fn put_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, v: T) -> bool {
    &&& new.locking_thread() == old.locking_thread()
    &&& new.is_init() == true
    &&& new.view() == v
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.control() == old.control()
    &&& new.being_killed() == old.being_killed()
}

pub open spec fn update_ghost_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool>(old: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new: RwLock<T, ROT, GhostT, HAS_KILL_STATE>, new_ghost: GhostT) -> bool {
    &&& new.locking_thread() == old.locking_thread()
    &&& new.is_init() == old.is_init()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == new_ghost
    &&& new.control() == old.control()
}

impl<T: LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const HAS_KILL_STATE: bool> LockOwnerIdTrait for RwLock<T, ROT, GhostT, HAS_KILL_STATE> {
    open spec fn container_depth(&self) -> LockOwnerId {
        if self.being_killed() { LockOwnerId::High }
        else {
            match self.view_rodata().container_source() {
                OwnerSource::Payload => self.view().container_depth(),
                OwnerSource::Fixed(owner) => owner,
                // Only a live write acquisition has a concrete dynamic owner; otherwise the lock reports `None`.
                OwnerSource::Dynamic => match self.lock_process_owner_u() { Some(owner) => owner, None => LockOwnerId::None },
            }
        }
    }
    open spec fn process_depth(&self) -> LockOwnerId {
        if self.being_killed() { LockOwnerId::High }
        else {
            match self.view_rodata().process_source() {
                OwnerSource::Payload => self.view().process_depth(),
                OwnerSource::Fixed(owner) => owner,
                // Only a live write acquisition has a concrete dynamic owner; otherwise the lock reports `None`.
                OwnerSource::Dynamic => match self.lock_process_owner_u() { Some(owner) => owner, None => LockOwnerId::None },
            }
        }
    }
}

impl<T: LockIdTrait, const HAS_KILL_STATE: bool> LockIdTrait for RwLock<T, (), (), HAS_KILL_STATE> {
    open spec fn lock_id(&self) -> LockId { self.view().lock_id() }
}
}

// Layout contract: `LockControl` has the size and alignment of `Option<KillerInfo>`, 56 bytes on 64-bit targets.
const _: () = assert!(core::mem::size_of::<LockControl>() == core::mem::size_of::<Option<KillerInfo>>());
const _: () = assert!(core::mem::align_of::<LockControl>() == core::mem::align_of::<Option<KillerInfo>>());
#[cfg(target_pointer_width = "64")]
const _: () = assert!(core::mem::size_of::<LockControl>() == 56);
