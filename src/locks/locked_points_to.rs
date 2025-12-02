use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use core::mem::MaybeUninit;
verus! {

impl<T> LockMinor for PointsTo<RwLock<T>>{
    open spec fn lock_minor(&self) -> LockMinorId{
        self.addr()
    }
}  

impl<T:LockOwnerIdUtil> LockOwnerIdUtil for PointsTo<RwLock<T>>{
    open spec fn container_depth(&self) -> LockOwnerId{
        self.value()@.container_depth()
    }
    open spec fn process_depth(&self) -> LockOwnerId{
        self.value()@.process_depth()
    }
}  

impl<T:LockedUtil> LockedUtil for PointsTo<RwLock<T>>{
    open spec fn inv(&self) -> bool{
        &&&
        self.is_init()
        &&&
        self.value()@.inv()
    }

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

#[verifier::external_body]
pub fn wlock<T:LockedUtil>(pptr:&PPtr<RwLock<T>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T>>>, Tracked(lock_manager): Tracked<&mut LockManager>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).lock_major_sat(lock_id@.major),
        old(perm).lock_minor() == lock_id@.minor,

        wlock_requires(old(perm).value(), old(lock_manager)),
        old(lock_manager).lock_id_valid(lock_id@),
    ensures
        perm.addr() == old(perm).addr(),
        perm.is_init(),

        wlock_ensures(old(perm).value(), perm.value(), lock_id@, lock_manager.thread_id(), ret@),
        lock_ensures(old(lock_manager), lock_manager, lock_id@),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T>>;
        (*uptr).assume_init_mut().wlock(Tracked(lock_manager), Ghost(lock_id@.major))
    }
}
#[verifier::external_body]
pub fn wunlock<T:LockedUtil>(pptr:&PPtr<RwLock<T>>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T>>>, Tracked(lock_manager): Tracked<&mut LockManager>, lock_perm: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).value().wlocked_by(old(lock_manager)),
        old(perm).value().being_killed() == false,
        old(perm).value().inv(),

        lock_perm@.state() is WriteLock,
        lock_perm@.thread_id() == old(lock_manager).thread_id(),
        lock_perm@.lock_id() == old(perm).value().locking_thread()->Write_lock_id,
    ensures
        old(perm).addr() == perm.addr(),
        perm.is_init(),

        perm.value().locking_thread() is None,

        wunlock_ensures(old(perm).value(), perm.value()),
        unlock_ensures(old(lock_manager), lock_manager, lock_perm@.lock_id()),
{
     unsafe {
        let uptr = pptr.addr() as *mut MaybeUninit<RwLock<T>>;
        (*uptr).assume_init_mut().wunlock(Tracked(lock_manager), lock_perm);
    }
}

}