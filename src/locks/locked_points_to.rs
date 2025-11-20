use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
verus! {

impl<T> LockMinor for PointsTo<RwLock<T>>{
    open spec fn lock_minor(&self) -> LockMinorId{
        self.addr()
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
fn wlock<T:LockedUtil>(pptr:&PPtr<T>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T>>>, Tracked(lock_manager): Tracked<&mut LockManager>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),

        old(perm).lock_major_sat(lock_id@.major),
        old(perm).lock_minor() == lock_id@.minor,

        old(perm).value().locked_by(old(lock_manager)) == false,
        old(lock_manager).lock_id_valid(lock_id@),
    ensures
        perm.addr() == old(perm).addr(),
        perm.is_init(),

        
{
    Tracked::assume_new()
}
#[verifier::external_body]
fn wunlock<T:LockedUtil>(pptr:&PPtr<T>, Tracked(perm): Tracked<&mut PointsTo<RwLock<T>>>, Tracked(lock_manager): Tracked<&mut LockManager>, lock_perm: Tracked<LockPerm>){

}

}