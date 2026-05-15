use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use core::mem::MaybeUninit;
verus! {

impl<T, ROT, GhostT, const HasKillState: bool> LockMinorTrait for PointsTo<RwLock<T, ROT, GhostT, HasKillState>>{
    open spec fn lock_minor(&self) -> LockMinorId{
        self.addr()
    }
}

impl<T:LockOwnerIdTrait, ROT, GhostT, const HasKillState: bool> LockOwnerIdTrait for PointsTo<RwLock<T, ROT, GhostT, HasKillState>>{
    open spec fn container_depth(&self) -> LockOwnerId{
        self.value()@.container_depth()
    }
    open spec fn process_depth(&self) -> LockOwnerId{
        self.value()@.process_depth()
    }
}  
impl<T:LockInvTrait, ROT, GhostT, const HasKillState: bool> LockInvTrait for PointsTo<RwLock<T, ROT, GhostT, HasKillState>>{
    open spec fn inv(&self) -> bool{
        &&&
        self.is_init()
        &&&
        self.value()@.inv()
    }
}
impl<T:LockMajorTrait, ROT, GhostT, const HasKillState: bool> LockMajorTrait for PointsTo<RwLock<T, ROT, GhostT, HasKillState>>{
    open spec fn lock_major_1(&self) -> LockMajorId {
        self.value()@.lock_major_1()
    }
    open spec fn lock_major_2(&self) -> LockMajorId {
        self.value()@.lock_major_2()
    }    
    open spec fn lock_major_3(&self) -> LockMajorId {
        self.value()@.lock_major_3()
    }    
    open spec fn lock_major_default(&self) -> LockMajorId {
        self.value()@.lock_major_default()
    }

    open spec fn lock_major_1_predicate(&self) -> bool{
        self.value()@.lock_major_1_predicate()
    }
    open spec fn lock_major_2_predicate(&self) -> bool{
        self.value()@.lock_major_2_predicate()
    }
    open spec fn lock_major_3_predicate(&self) -> bool{
        self.value()@.lock_major_3_predicate()
    }
    open spec fn lock_major_default_predicate(&self) -> bool{
        self.value()@.lock_major_default_predicate()
    }
}  


// TODO
#[verifier::external_body]
pub fn wlock<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, GhostT,>(pptr:&PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).lock_major_sat(lock_id@.major),
        old(perm).lock_minor() == lock_id@.minor,

        wlock_requires(old(perm).value(), old(lctx)),
        old(lctx).lock_id_acyclic(lock_id@),
    ensures
        perm.addr() == old(perm).addr(),
        perm.is_init(),

        wlock_ensures(old(perm).value(), perm.value(), lock_id@, lctx.thread_id(), ret@),
        lock_ensures(old(lctx), lctx, perm.value().view(), lock_id@),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().wlock_external(Tracked(lctx))
    }
}

// TODO
#[verifier::external_body]
pub fn wunlock<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, GhostT,>(pptr:&PPtr<RwLock<T, ROT, GhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),

        lock_perm@.state() is WriteLock,
        lock_perm@.thread_id() == old(lctx).thread_id(),
        lock_perm@.lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == perm.addr(),
        perm.is_init(),

        perm.value().locking_thread() is None,

        wunlock_ensures(old(perm).value(), perm.value()),
        unlock_ensures(old(lctx), lctx, perm.value().view(), lock_perm@.lock_id()),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().wunlock_external(Tracked(lctx), lock_perm);
    }
}

#[verifier::external_body]
pub fn take<T, ROT, GhostT, const HasKillState: bool>(pptr:&PPtr<RwLock<T, ROT, GhostT, HasKillState>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HasKillState>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret:T)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).value().wlocked_by(lctx),
        old(perm).value().is_init(),

        lock_perm@.state() is WriteLock,
        lock_perm@.thread_id() == lctx.thread_id(),
        lock_perm@.lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == perm.addr(),
        perm.is_init(),

        take_ensures(old(perm).value(), perm.value()),

        ret == old(perm).value()@
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HasKillState>>;
        (*uptr).assume_init_mut().take(Tracked(lctx),lock_perm)
    }
}


#[verifier::external_body]
pub fn put<T, ROT, GhostT, const HasKillState: bool>(pptr:&PPtr<RwLock<T, ROT, GhostT, HasKillState>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, GhostT, HasKillState>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>, v: T) 
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).value().wlocked_by(lctx),
        old(perm).value().is_init() == false,

        lock_perm@.state() is WriteLock,
        lock_perm@.thread_id() == lctx.thread_id(),
        lock_perm@.lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == perm.addr(),
        perm.is_init(),

        put_ensures(old(perm).value(), perm.value(), v),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, GhostT, HasKillState>>;
        (*uptr).assume_init_mut().put(Tracked(lctx), lock_perm,v)
    }
}
#[verifier::external_body]
pub fn borrow<'a, T, ROT, GhostT, const HasKillState: bool>(pptr:&PPtr<RwLock<T, ROT, GhostT, HasKillState>>, Tracked(perm): Tracked<& PointsTo<RwLock<T, ROT, GhostT, HasKillState>>>, lock_perm: Tracked<&'a LockPerm>) -> (ret:&'a T)
    requires
        pptr.addr() == perm.addr(),
        perm.is_init(),

        perm.value().is_init(),

        lock_perm@.state() is WriteLock ==> perm.value().write_lock_perm_match(lock_perm@),
        lock_perm@.state() is ReadLock ==> perm.value().read_lock_perm_match(lock_perm@), 
    ensures
        ret == perm.value().view(),
{
     unsafe {
        let uptr = &*(pptr.addr() as *mut RwLock<T, ROT, GhostT, HasKillState>);
        uptr.borrow(lock_perm)
    }
}

#[verifier::external_body]
pub fn borrow_rodata<'a, T, ROT, GhostT, const HasKillState: bool>(pptr:&PPtr<RwLock<T, ROT, GhostT, HasKillState>>, Tracked(perm): Tracked<&'a PointsTo<RwLock<T, ROT, GhostT, HasKillState>>>) -> (ret:&'a ROT)
    requires
        pptr.addr() == perm.addr(),
        perm.is_init(),
    ensures
        ret == perm.value().view_rodata(),
{
     unsafe {
        let uptr = &*(pptr.addr() as *mut RwLock<T, ROT, GhostT, HasKillState>);
        uptr.borrow_rodata()
    }
}


}