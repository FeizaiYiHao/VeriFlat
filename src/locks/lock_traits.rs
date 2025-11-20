use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
verus! {

pub trait LockedUtil {
    spec fn inv(&self) -> bool;

    spec fn lock_major_1(&self) -> LockMajorId;
    spec fn lock_major_2(&self) -> LockMajorId;
    spec fn lock_major_3(&self) -> LockMajorId;
    spec fn lock_major_default(&self) -> LockMajorId;

    spec fn lock_major_1_predicate(&self) -> bool;
    spec fn lock_major_2_predicate(&self) -> bool;
    spec fn lock_major_3_predicate(&self) -> bool;
    spec fn lock_major_default_predicate(&self) -> bool;

    
    open spec fn lock_major_sat(&self, lock_major: LockMajorId) -> bool{
        if lock_major == self.lock_major_1(){
            self.lock_major_1_predicate()
        }
        else if lock_major == self.lock_major_2(){
            self.lock_major_2_predicate()
        }
        else if lock_major == self.lock_major_3(){
            self.lock_major_3_predicate()
        }
        else {
            lock_major == self.lock_major_default()
        }
    }
}

pub trait LockMinor{
    spec fn lock_minor(&self) -> LockMinorId;
}

impl<T> LockMinor for PointsTo<RwLock<T>>{
    open spec fn lock_minor(&self) -> LockMinorId{
        self.addr()
    }
}  

impl<T:LockedUtil> LockedUtil for PointsTo<RwLock<T>>{
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

}