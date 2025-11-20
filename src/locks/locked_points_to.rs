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

pub trait PPtrRwLockAdditionalFns<T>{
    fn wlock(self, Tracked(perm): Tracked<&mut PointsTo<RwLock<T>>>, lock_id: Ghost<LockId>) -> Tracked<LockPerm>;
    fn wunlock(self, Tracked(perm): Tracked<&mut PointsTo<RwLock<T>>>, lock_perm: Tracked<LockPerm>);
}

impl<T:LockedUtil> PPtrRwLockAdditionalFns<T> for PPtr<T>{
    #[verifier::external_body]
    fn wlock(self, Tracked(perm): Tracked<&mut PointsTo<RwLock<T>>>, lock_id: Ghost<LockId>) -> Tracked<LockPerm>{
        Tracked::assume_new()
    }
    #[verifier::external_body]
    fn wunlock(self, Tracked(perm): Tracked<&mut PointsTo<RwLock<T>>>, lock_perm: Tracked<LockPerm>){

    }
}

}