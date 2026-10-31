use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
/// A single lock over token storage: the lock lives in memory outside this value, reached only through its address;
/// this value holds that address and the lock's points-to token.
#[verifier::reject_recursive_types(T)]
pub struct TokenLock<T, ROT, GhostT, const HAS_KILL_STATE: bool> {
    base: usize,
    perm: Tracked<PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>,
}

impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> TokenLock<T, ROT, GhostT, HAS_KILL_STATE> {
    /// The lock object the token covers.
    pub closed spec fn lock(&self) -> RwLock<T, ROT, GhostT, HAS_KILL_STATE> { self.perm@.value() }

    /// The token covers an initialized lock at the held address.
    pub closed spec fn wf(&self) -> bool { self.perm@.is_init() && self.perm@.addr() == self.base }

    pub open spec fn is_init(&self) -> bool { self.wf() && self.lock().is_init() }
    pub open spec fn view(&self) -> T { self.lock().view() }
    pub open spec fn view_rodata(&self) -> ROT { self.lock().view_rodata() }
    pub open spec fn view_ghost(&self) -> GhostT { self.lock().view_ghost() }
    pub open spec fn locking_thread(&self) -> RwLockState { self.lock().locking_thread() }
    pub open spec fn locked(&self) -> bool { self.lock().locked() }
    pub open spec fn wlocked_by(&self, lctx: &LocalContext) -> bool { self.lock().wlocked_by(lctx) }
    pub open spec fn wlocked_by_thread(&self, thread_id: LockThreadId) -> bool { self.lock().wlocked_by_thread(thread_id) }
    pub open spec fn locked_by_thread(&self, thread_id: LockThreadId) -> bool { self.lock().locked_by_thread(thread_id) }
    pub open spec fn write_lock_perm_match(&self, lock_perm: &LockPerm) -> bool { self.lock().write_lock_perm_match(lock_perm) }
    pub open spec fn being_killed(&self) -> bool { self.lock().being_killed() }

    /// Takes the lock at `addr` through its points-to token.
    pub fn from_token(addr: usize, perm: Tracked<PointsTo<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>>) -> (ret: Self)
        requires
            perm@.is_init(),
            perm@.addr() == addr,
        ensures
            ret.wf(),
            ret.lock() == perm@.value(),
    {
        Self { base: addr, perm }
    }

    pub fn borrow<'a>(&self, lp: Tracked<&'a LockPerm>) -> (ret: &'a T)
        requires
            self.is_init(),
            lp.view().state() is WriteLock ==> self.write_lock_perm_match(lp.view()),
            lp.view().state() is ReadLock ==> self.lock().read_lock_perm_match(lp.view()),
        ensures
            ret == self.view(),
    {
        let tracked perm = self.perm.borrow();
        borrow(&PPtr::<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>::from_usize(self.base), Tracked(perm), lp)
    }

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
            final(self).view_rodata() == old(self).view_rodata(),
            final(self).view_ghost() == old(self).view_ghost(),
            final(self).locking_thread() == old(self).locking_thread(),
            final(self).lock().control() == old(self).lock().control(),
            *ret == old(self).view(),
            final(self).view() == *final(ret),
    {
        let addr = self.base;
        let tracked perm = self.perm.borrow_mut();
        borrow_mut(&PPtr::<RwLock<T, ROT, GhostT, HAS_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lp)
    }
}

impl<T: LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool> TokenLock<T, ROT, GhostT, HAS_KILL_STATE> {
    pub open spec fn inv(&self) -> bool { self.wf() && self.lock().inv() }
}

impl<T: LockIdTrait, const HAS_KILL_STATE: bool> LockIdTrait for TokenLock<T, (), (), HAS_KILL_STATE> {
    open spec fn lock_id(&self) -> LockId { self.view().lock_id() }
}

impl<T: LockInvTrait + LockMajorTrait + LockMinorTrait + LockOwnerIdTrait, ROT, GhostT> TokenLock<T, ROT, GhostT, NO_KILL_STATE> {
    pub fn wlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            old(self).view().container_depth() == lock_id.view().container,
            old(self).view().process_depth() == lock_id.view().process,
            old(self).view().lock_major_sat(lock_id.view().major),
            old(self).view().lock_minor() == lock_id.view().minor,
            wlock_requires(old(self).lock(), old(lctx)),
            old(lctx).lock_id_acyclic(lock_id.view()),
        ensures
            final(self).inv(),
            wlock_ensures(old(self).lock(), final(self).lock(), lock_id.view(), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), lock_id.view(), obj_id.view()),
    {
        let addr = self.base;
        let tracked perm = self.perm.borrow_mut();
        wlock_with_lock_id(&PPtr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lock_id, obj_id)
    }

    pub fn wunlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, obj_id: Ghost<KernelObjId>)
        requires
            old(self).inv(),
            old(self).wlocked_by(old(lctx)),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            lp.view().lock_id() == old(self).locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(LockId { container: old(self).view().container_depth(), process: old(self).view().process_depth(), major: old(self).view().current_lock_major(), minor: old(self).view().lock_minor() }, obj_id.view()),
        ensures
            final(self).inv(),
            wunlock_ensures(old(self).lock(), final(self).lock()),
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), LockId {
                container: old(self).view().container_depth(), process: old(self).view().process_depth(), major: old(self).view().current_lock_major(), minor: old(self).view().lock_minor() }),
    {
        let lock_id = Ghost(LockId { container: self.view().container_depth(), process: self.view().process_depth(), major: self.view().current_lock_major(), minor: self.view().lock_minor() });
        let addr = self.base;
        let tracked perm = self.perm.borrow_mut();
        no_kill_state_wunlock_with_lock_id(&PPtr::<RwLock<T, ROT, GhostT, NO_KILL_STATE>>::from_usize(addr), Tracked(perm), Tracked(lctx), lp, lock_id, obj_id);
    }
}
}
