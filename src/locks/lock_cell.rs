use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::{define::*};
use crate::locks::*;

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

/// Ghost control state of a lock. Non-dynamic locks use only `Clear` and `Killed`; a dynamic lock records the concrete
/// owner of its current write acquisition as `DynamicProcess`. Only that owner and the kill mark reach the runtime word.
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
    Killed(Ghost<KillerInfo>),
    DepthConflict { observed_owner: LockOwnerId },
}

/// Observable mode of a lock, independent of ownership and reader count.
pub ghost enum LockStateU { Unlocked, ReadLocked, WriteLocked }

pub enum RwLockState {
    Write { thread_id: LockThreadId, lock_id: LockToken },
    Read { reader_map: Map<LockThreadId, LockToken> },
    None,
}

/// `LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>`: payload `T` under the runtime lock word `I`.
///
/// The refinement projection alone decides which payload and ghost fields are
/// user-visible. Ghost replacement is proof-only and independent of payload
/// locking; callers close the affected invariants at the kernel boundary.
#[repr(C)]
pub struct LockCell<T, ROT, GhostT, const HAS_KILL_STATE: bool, I = SpinWord> {
    pub(crate) lock: I,
    pub(crate) value: T,
    pub(super) read_only_value: ROT,
    ghost_value: Ghost<GhostT>,

    control: Ghost<LockControl>,
    is_init: Ghost<bool>,
    locking_thread: Ghost<RwLockState>,
}

/// Tracked token of one lock cell: `addr()`, `is_init()`, `value()`; `value()` is exact only while this CPU holds the lock, otherwise the snapshot from the last step boundary.
pub type LockObjPerm<T, ROT, GhostT, const HAS_KILL_STATE: bool, I = SpinWord> = PointsTo<LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>>;

impl<T, ROT, GhostT, const HAS_KILL_STATE: bool, I: SpinLockInner> LockCell<T, ROT, GhostT, HAS_KILL_STATE, I> {
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
            lock: I::new_unlocked(),
            value, read_only_value, ghost_value: Ghost(ghost_value), control: Ghost(LockControl::Clear), is_init: Ghost(true), locking_thread: Ghost(RwLockState::None),
        }
    }

    /// TCB: runtime image of a freshly retyped object that its creator holds write-locked under `control` (`Clear`, or
    /// `DynamicProcess` for a dynamic lock); `owner` is the owner `control` records (`None` for `Clear`). Only the retype
    /// primitives use it; their contracts supply the ghost state.
    #[verifier::external]
    pub fn new_wlocked_for_retype(value: T, read_only_value: ROT, control: Ghost<LockControl>, owner: LockOwnerId) -> Self {
        Self {
            lock: I::new_wlocked_for_retype(owner),
            value, read_only_value, ghost_value: Ghost::assume_new(), control, is_init: Ghost::assume_new(), locking_thread: Ghost::assume_new(),
        }
    }
}

impl<T, ROT, GhostT, const HAS_KILL_STATE: bool, I> LockCell<T, ROT, GhostT, HAS_KILL_STATE, I> {
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
    pub closed spec fn control(&self) -> LockControl { self.control.view() }
    pub open spec fn killer_info_from_control(&self) -> Option<KillerInfo> {
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
        if HAS_KILL_STATE { self.killer_info_from_control() } else { None }
    }
    pub open spec fn being_killed(&self) -> bool {
        if HAS_KILL_STATE { self.killer_info_from_control() is Some } else { false }
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

impl<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I> LockCell<T, ROT, GhostT, HAS_KILL_STATE, I> {
    pub open spec fn inv(&self) -> bool {
        &&& self.view().inv()
        &&& self.is_init()
        &&& self.locking_thread() is Read ==> !self.locking_thread()->Read_reader_map.dom().is_empty()
    }
}

impl<T, ROT, GhostT, const HAS_KILL_STATE: bool, I> LockCell<T, ROT, GhostT, HAS_KILL_STATE, I> {
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
            // Invariants of the lock are preserved by the structure of the lock cell.
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
}

pub open spec fn wlock_requires<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, lctx: &LocalContext) -> bool {
    &&& old.inv()
    // The acquiring thread must hold neither a read nor a write lock here; other
    // threads' contention is handled by the physical lock.
    &&& old.locked_by(lctx) == false
    &&& lctx.kernel_view_locking_state() is Acquire
}

pub open spec fn wlock_ensures<T: LockInvTrait + LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, lock_id: LockId, lctx: &LocalContext, lock_perm: LockPerm) -> bool {
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
pub open spec fn rlock_ensures<T: LockInvTrait + LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, lock_id: LockId, lctx: &LocalContext, lock_perm: LockPerm) -> bool {
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

pub open spec fn runlock_ensures<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, thread_id: LockThreadId) -> bool {
    &&& new.locking_thread() == (if old.locking_thread()->Read_reader_map.remove(thread_id).dom().is_empty() { RwLockState::None } else { RwLockState::Read { reader_map: old.locking_thread()->Read_reader_map.remove(thread_id) } })
    &&& new.inv()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.being_killed() == old.being_killed()
    &&& new.control() == old.control()
}

pub open spec fn wunlock_ensures<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>) -> bool {
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
pub open spec fn dynamic_wlock_ensures<T: LockInvTrait + LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I>(
    old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, old_lctx: &LocalContext, new_lctx: &LocalContext,
    lock_id: LockId, obj_id: KernelObjId, requested: LockOwnerId, ret: DynamicWLockResult,
) -> bool {
    match ret {
        DynamicWLockResult::Killed(killer_info) => {
            &&& old.killer_info_from_control() == Some(killer_info.view())
            &&& new == old
            &&& *new_lctx == *old_lctx
        },
        DynamicWLockResult::DepthConflict { observed_owner } => {
            &&& old.killer_info_from_control() is None
            &&& old.wlocked()
            &&& old.dynamic_process_owner() == Some(observed_owner)
            &&& observed_owner < requested
            &&& new == old
            &&& *new_lctx == *old_lctx
        },
        DynamicWLockResult::Acquired(lock_perm) => {
            &&& old.killer_info_from_control() is None
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
pub open spec fn dynamic_wunlock_ensures<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>) -> bool {
    &&& new.locking_thread() == RwLockState::None
    &&& new.inv()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.control() == LockControl::Clear
}

/// The writer becomes the only reader under its write token; payload, ghost slot, and kill state stay.
pub open spec fn downgrade_ensures<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, lctx: &LocalContext, old_perm: LockPerm, new_perm: LockPerm) -> bool {
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

pub open spec fn take_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>) -> bool {
    &&& new.locking_thread() == old.locking_thread()
    &&& new.is_init() == false
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.control() == old.control()
}

pub open spec fn put_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, v: T) -> bool {
    &&& new.locking_thread() == old.locking_thread()
    &&& new.is_init() == true
    &&& new.view() == v
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == old.view_ghost()
    &&& new.control() == old.control()
    &&& new.being_killed() == old.being_killed()
}

pub open spec fn update_ghost_ensures<T, ROT, GhostT, const HAS_KILL_STATE: bool, I>(old: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new: LockCell<T, ROT, GhostT, HAS_KILL_STATE, I>, new_ghost: GhostT) -> bool {
    &&& new.locking_thread() == old.locking_thread()
    &&& new.is_init() == old.is_init()
    &&& new.view() == old.view()
    &&& new.view_rodata() == old.view_rodata()
    &&& new.view_ghost() == new_ghost
    &&& new.control() == old.control()
}

impl<T: LockOwnerIdTrait, ROT: LockOwnerIdTrait, GhostT, const HAS_KILL_STATE: bool, I> LockOwnerIdTrait for LockCell<T, ROT, GhostT, HAS_KILL_STATE, I> {
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

impl<T: LockIdTrait, const HAS_KILL_STATE: bool, I> LockIdTrait for LockCell<T, (), (), HAS_KILL_STATE, I> {
    open spec fn lock_id(&self) -> LockId { self.view().lock_id() }
}
}
