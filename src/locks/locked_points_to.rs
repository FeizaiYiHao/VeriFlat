use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use core::mem::MaybeUninit;
verus! {

impl<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> LockMinorTrait for PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>{
    open spec fn lock_minor(&self) -> LockMinorId{
        self.addr()
    }
}


impl<T:LockOwnerIdTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT, const HAS_KILL_STATE: bool> LockOwnerIdTrait for PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>{
    open spec fn container_depth(&self) -> LockOwnerId{
        if self.value().view_rodata().container_depth() != LockOwnerId::NotApp{
            self.value().view_rodata().container_depth()
        }else{
            self.value()@.container_depth()
        }
    }
    open spec fn process_depth(&self) -> LockOwnerId{
        if self.value().view_rodata().process_depth() != LockOwnerId::NotApp{
            self.value().view_rodata().process_depth()
        }else{
            self.value()@.process_depth()
        }
    }
}  
impl<T:LockInvTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> LockInvTrait for PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>{
    open spec fn inv(&self) -> bool{
        &&&
        self.is_init()
        &&&
        self.value()@.inv()
    }
}
impl<T:LockMajorTrait, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool> LockMajorTrait for PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>{
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
pub fn wlock<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,>(pptr:&PPtr<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).container_depth() == lock_id@.container,
        old(perm).process_depth() == lock_id@.process,
        old(perm).lock_major_sat(lock_id@.major),
        old(perm).lock_minor() == lock_id@.minor,

        wlock_requires(old(perm).value(), old(lctx)),
        old(lctx).lock_id_acyclic(lock_id@),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),

        wlock_ensures(old(perm).value(), final(perm).value(), lock_id@, final(lctx).thread_id(), ret@),
        lock_ensures(old(lctx), final(lctx), final(perm).value().view(), lock_id@),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().wlock_external(Tracked(lctx))
    }
}

// TODO
#[verifier::external_body]
pub fn wunlock<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT,>(pptr:&PPtr<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),

        lock_perm@.state() is WriteLock,
        lock_perm@.thread_id() == old(lctx).thread_id(),
        lock_perm@.lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),

        final(perm).value().locking_thread() is None,

        wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), final(perm).value().view(), lock_perm@.lock_id()),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, KGhostT, UGhostT, NO_KILL_STATE>>;
        (*uptr).assume_init_mut().wunlock_external(Tracked(lctx), lock_perm);
    }
}

#[verifier::external_body]
pub fn wlock_unless_killed<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT: LockOwnerIdTrait, KGhostT, UGhostT,>(pptr:&PPtr<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret: (bool, Option<Tracked<LockPerm>>))
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).container_depth() == lock_id@.container,
        old(perm).process_depth() == lock_id@.process,
        old(perm).lock_major_sat(lock_id@.major),
        old(perm).lock_minor() == lock_id@.minor,

        wlock_requires(old(perm).value(), old(lctx)),
        old(lctx).lock_id_acyclic(lock_id@),
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),

        final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        final(lctx).user_view_locking_state() == old(lctx).user_view_locking_state(),

        ret.0 == false ==> 
        {
            &&&
            old(perm).value().being_killed() == true
            &&&
            old(perm).value() == final(perm).value()
            &&&
            ret.1 is None
        },
        ret.0 == true ==>{
            &&&                
            old(perm).value().being_killed() == false
            &&&
            ret.1 is Some
            &&&
            wlock_ensures(old(perm).value(), final(perm).value(), lock_id@, final(lctx).thread_id(), ret.1.unwrap()@)
            &&&
            lock_ensures(old(lctx), final(lctx), final(perm).value().view(), lock_id@)
        },
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().wlock_unless_killed(Tracked(lctx), lock_id)
    }
}

#[verifier::external_body]
pub fn has_kill_state_wunlock<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait + LockUserVisibilityTrait, ROT, KGhostT, UGhostT,>(pptr:&PPtr<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).value().wlocked_by(old(lctx)),
        old(perm).value().inv(),

        lock_perm@.state() is WriteLock,
        lock_perm@.thread_id() == old(lctx).thread_id(),
        lock_perm@.lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),

        final(perm).value().locking_thread() is None,

        old(perm).value().being_killed() == final(perm).value().being_killed(),
        wunlock_ensures(old(perm).value(), final(perm).value()),
        unlock_ensures(old(lctx), final(lctx), final(perm).value().view(), lock_perm@.lock_id()),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().wunlock(Tracked(lctx), lock_perm);
    }
}

#[verifier::external_body]
pub fn take<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(pptr:&PPtr<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret:T)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).value().wlocked_by(lctx),
        old(perm).value().is_init(),

        lock_perm@.state() is WriteLock,
        lock_perm@.thread_id() == lctx.thread_id(),
        lock_perm@.lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),

        take_ensures(old(perm).value(), final(perm).value()),

        ret == old(perm).value()@
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().take(Tracked(lctx),lock_perm)
    }
}


#[verifier::external_body]
pub fn put<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(pptr:&PPtr<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>, v: T) 
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).value().wlocked_by(lctx),
        old(perm).value().is_init() == false,

        lock_perm@.state() is WriteLock,
        lock_perm@.thread_id() == lctx.thread_id(),
        lock_perm@.lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == final(perm).addr(),
        final(perm).is_init(),

        put_ensures(old(perm).value(), final(perm).value(), v),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>;
        (*uptr).assume_init_mut().put(Tracked(lctx), lock_perm,v)
    }
}
#[verifier::external_body]
pub fn borrow<'a, T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(pptr:&PPtr<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<& PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>, lock_perm: Tracked<&'a LockPerm>) -> (ret:&'a T)
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
        let uptr = &*(pptr.addr() as *mut RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>);
        uptr.borrow(lock_perm)
    }
}

#[verifier::external_body]
pub fn borrow_rodata<'a, T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>(pptr:&PPtr<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>, Tracked(perm): Tracked<&'a PointsTo<RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>>>) -> (ret:&'a ROT)
    requires
        pptr.addr() == perm.addr(),
        perm.is_init(),
    ensures
        ret == perm.value().view_rodata(),
{
     unsafe {
        let uptr = &*(pptr.addr() as *mut RwLock<T, ROT, KGhostT, UGhostT, HAS_KILL_STATE>);
        uptr.borrow_rodata()
    }
}


}
