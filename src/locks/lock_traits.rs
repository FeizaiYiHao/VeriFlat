use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
verus! {

pub trait LockInvTrait{
    spec fn inv(&self) -> bool;
}

pub trait LockMajorTrait {
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
        else if lock_major == self.lock_major_default(){
            self.lock_major_default_predicate()
        }else{
            false
        }
    }
}

pub trait LockOwnerIdTrait {
    spec fn container_depth(&self) -> LockOwnerId;
    spec fn process_depth(&self) -> LockOwnerId;
}

pub trait LockMinorTrait {
    spec fn lock_minor(&self) -> LockMinorId;
}

pub trait LockKillTrait {
    spec fn is_being_killed(&self) -> bool;
}

}