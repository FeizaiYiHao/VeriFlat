use vstd::prelude::*;
use crate::{define::*};
use core::sync::atomic::*;

use super::*;
use crate::primitive::*;

verus! {
    #[verifier::reject_recursive_types(T)]
    pub struct LockedArrayElement<T, ROT, GhostT, const HAS_KILL_STATE: bool>{
        pub value: RwLock<T, ROT, GhostT, HAS_KILL_STATE>,
        pub lock_minor: LockMinorId, 
    }
    impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> LockedArrayElement<T, ROT, GhostT, HAS_KILL_STATE>{
        pub open spec fn view(&self) -> RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
            self.value
        }
        pub open spec fn value(&self) -> RwLock<T, ROT, GhostT, HAS_KILL_STATE>{
            self.value
        }
    }

    impl<T, ROT, GhostT, const HAS_KILL_STATE: bool> LockMinorTrait for LockedArrayElement<T, ROT, GhostT, HAS_KILL_STATE>{
        open spec fn lock_minor(&self) -> LockMinorId {
            self.lock_minor
        }
    }

    impl<T:LockInvTrait, ROT, GhostT, const HAS_KILL_STATE: bool> LockInvTrait for LockedArrayElement<T, ROT, GhostT, HAS_KILL_STATE>{
        open spec fn inv(&self) -> bool {
            self.view().inv()
        }
    }

    impl<T:LockMajorTrait, ROT, GhostT, const HAS_KILL_STATE: bool> LockMajorTrait for LockedArrayElement<T, ROT, GhostT, HAS_KILL_STATE>{
        open spec fn lock_major_1(&self) -> LockMajorId {
            self.view().view().lock_major_1()
        }
    
        open spec fn lock_major_2(&self) -> LockMajorId {
            self.view().view().lock_major_2()
        }
    
        open spec fn lock_major_3(&self) -> LockMajorId {
            self.view().view().lock_major_3()
        }
    
        open spec fn lock_major_default(&self) -> LockMajorId {
            self.view().view().lock_major_default()
        }
    
        open spec fn lock_major_1_predicate(&self) -> bool {
            self.view().view().lock_major_1_predicate()
        }
    
        open spec fn lock_major_2_predicate(&self) -> bool {
            self.view().view().lock_major_2_predicate()
        }
    
        open spec fn lock_major_3_predicate(&self) -> bool {
            self.view().view().lock_major_3_predicate()
        }
    
        open spec fn lock_major_default_predicate(&self) -> bool {
            self.view().view().lock_major_default_predicate()
        }
    }
    
    impl<T:LockOwnerIdTrait, ROT, GhostT, const HAS_KILL_STATE: bool> LockOwnerIdTrait for LockedArrayElement<T, ROT, GhostT, HAS_KILL_STATE>{
        open spec fn container_depth(&self) -> LockOwnerId {
            self.view().view().container_depth()
        }
    
        open spec fn process_depth(&self) -> LockOwnerId {
            self.view().view().process_depth()
        }
    }

    impl<T:LockInvTrait + LockMajorTrait + LockOwnerIdTrait, ROT, GhostT, const HAS_KILL_STATE: bool> LockedArrayElement<T, ROT, GhostT, HAS_KILL_STATE>{
        pub open spec fn lock_id(&self) -> LockId {
            LockId{
                container: self.container_depth(),
                process: self.process_depth(),
                major: self.view().view().current_lock_major(),
                minor: self.lock_minor(),
            }
        }
    }
    
}
