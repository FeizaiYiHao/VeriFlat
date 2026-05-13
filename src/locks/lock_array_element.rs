use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;
use crate::concurrency::*;

use super::*;
use crate::primitive::*;

verus! {
    #[verifier::reject_recursive_types(T)]
    pub struct LockedArrayElement<T, ROT, GhostT, const HasKillState: bool>{
        pub value: RwLock<T, ROT, GhostT, HasKillState>,
        pub lock_minor: LockMinorId, 
    }
    impl<T, ROT, GhostT, const HasKillState: bool> LockedArrayElement<T, ROT, GhostT, HasKillState>{
        pub open spec fn view(&self) -> RwLock<T, ROT, GhostT, HasKillState>{
            self.value
        }
        pub open spec fn value(&self) -> RwLock<T, ROT, GhostT, HasKillState>{
            self.value
        }
    }

    impl<T, ROT, GhostT, const HasKillState: bool> LockMinorTrait for LockedArrayElement<T, ROT, GhostT, HasKillState>{
        open spec fn lock_minor(&self) -> LockMinorId {
            self.lock_minor
        }
    }

    impl<T:LockInvTrait, ROT, GhostT, const HasKillState: bool> LockInvTrait for LockedArrayElement<T, ROT, GhostT, HasKillState>{
        open spec fn inv(&self) -> bool {
            self@.inv()
        }
    }

    impl<T:LockMajorTrait, ROT, GhostT, const HasKillState: bool> LockMajorTrait for LockedArrayElement<T, ROT, GhostT, HasKillState>{
        open spec fn lock_major_1(&self) -> LockMajorId {
            self@@.lock_major_1()
        }
    
        open spec fn lock_major_2(&self) -> LockMajorId {
            self@@.lock_major_2()
        }
    
        open spec fn lock_major_3(&self) -> LockMajorId {
            self@@.lock_major_3()
        }
    
        open spec fn lock_major_default(&self) -> LockMajorId {
            self@@.lock_major_default()
        }
    
        open spec fn lock_major_1_predicate(&self) -> bool {
            self@@.lock_major_1_predicate()
        }
    
        open spec fn lock_major_2_predicate(&self) -> bool {
            self@@.lock_major_2_predicate()
        }
    
        open spec fn lock_major_3_predicate(&self) -> bool {
            self@@.lock_major_3_predicate()
        }
    
        open spec fn lock_major_default_predicate(&self) -> bool {
            self@@.lock_major_default_predicate()
        }
    }
    
    impl<T:LockOwnerIdTrait, ROT, GhostT, const HasKillState: bool> LockOwnerIdTrait for LockedArrayElement<T, ROT, GhostT, HasKillState>{
        open spec fn container_depth(&self) -> LockOwnerId {
            self.view().view().container_depth()
        }
    
        open spec fn process_depth(&self) -> LockOwnerId {
            self.view().view().process_depth()
        }
    }
    
}